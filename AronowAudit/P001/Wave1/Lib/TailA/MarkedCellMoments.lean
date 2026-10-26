import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectAssembly
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectPairTruncated
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectOriginalLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectSampling
import AronowAudit.P001.Wave1.Lib.TailA.ReuseMoments
import AronowAudit.P001.Wave1.Lib.TailA.RareCounts
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellIntegrals
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellBoundaries
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellLocalization
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellPartitionMarks
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellSurvival

/-! Pinned matching-cell moment integrands, uniform bounds, and second-moment limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellMoments (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Average a measurable family over the actual finite resampling law. -/
theorem marked_resampling_average_measurable {E : Type*} [MeasurableSpace E]
    (n : ℕ) (f : E → (Fin n → Fin n) → ℝ)
    (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => mean (UniformResampling n) (f x)) := by
  simp only [uniform_resampling_mean]
  exact (Finset.measurable_sum _ (fun a _ => hf a)).div_const _

/-- The mean over two independent finite maps, conditional on the same original sample. -/
theorem marked_replica_product (n : ℕ) (f : (Fin n → Fin n) → ℝ) :
    mean (UniformResampling n) (fun a =>
      mean (UniformResampling n) (fun b => f a * f b)) =
        (mean (UniformResampling n) f)^2 := by
  simp only [mean, integral_const_mul, integral_mul_const]
  ring

/-- Conditional second moments dominate the conditional two-replica product. -/
theorem marked_replica_product_le (n : ℕ) (f : (Fin n → Fin n) → ℝ) :
    mean (UniformResampling n) (fun a =>
      mean (UniformResampling n) (fun b => f a * f b)) ≤
        mean (UniformResampling n) (fun a => (f a)^2) := by
  let c := mean (UniformResampling n) f
  have hpos : 0 ≤ mean (UniformResampling n) (fun a => (f a-c)^2) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : mean (UniformResampling n) (fun a => (f a-c)^2) =
      mean (UniformResampling n) (fun a => (f a)^2) - c^2 := by
    have hpoint : (fun a => (f a-c)^2) = fun a => (f a)^2-2*c*f a+c^2 := by
      funext a
      ring
    rw [hpoint, mean, integral_add
      (f := fun a => (f a)^2-2*c*f a) (g := fun _ => c^2)
      Integrable.of_finite Integrable.of_finite,
      integral_sub (f := fun a => (f a)^2) (g := fun a => 2*c*f a)
        Integrable.of_finite Integrable.of_finite,
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    change mean (UniformResampling n) (fun a => (f a)^2) - 2*c*c+c^2 = _
    ring
  rw [marked_replica_product]
  rw [heq] at hpos
  dsimp [c] at hpos
  linarith


/-- All three integrands have one bound uniform in sample size and pinned score. -/
theorem marked_pinned_integrands_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ),
      p ∈ Set.Icc (1/4 : ℝ) (3/4) →
      |mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2)| ≤ C ∧
      |mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
        (fun a => (U (pin n p z) a 0)^2))| ≤ C ∧
      |mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
        (fun a => mean (UniformResampling (n+1))
          (fun b => U (pin n p z) a 0 * U (pin n p z) b 0)))| ≤ C := by
  obtain ⟨C,hC,_,hpin⟩ := uniform_reuse_moments 2 (by norm_num)
  refine ⟨C,hC,fun n p hp => ?_⟩
  obtain ⟨hW,hU⟩ := hpin n p hp
  have hW0 : 0 ≤ mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hU0 : 0 ≤ mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun a => (U (pin n p z) a 0)^2)) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  refine ⟨by rwa [abs_of_nonneg hW0], by rwa [abs_of_nonneg hU0], ?_⟩
  have hcross0 : 0 ≤ mean (MatchProduct n) (fun z =>
      mean (UniformResampling (n+1)) (fun a => mean (UniformResampling (n+1))
        (fun b => U (pin n p z) a 0 * U (pin n p z) b 0))) := by
    exact integral_nonneg (fun z => by
      rw [marked_replica_product (n+1) (fun a => U (pin n p z) a 0)]
      exact sq_nonneg _)
  rw [abs_of_nonneg hcross0]
  apply le_trans _ hU
  apply integral_mono_of_nonneg
  · exact ae_of_all _ (fun z => by
      change (0 : ℝ) ≤ mean (UniformResampling (n+1)) (fun a =>
        mean (UniformResampling (n+1)) (fun b =>
          U (pin n p z) a 0 * U (pin n p z) b 0))
      rw [marked_replica_product (n+1) (fun a => U (pin n p z) a 0)]
      exact sq_nonneg _)
  · have hpinmap := reuse_pin_map_measurable n p
    exact (integrable_map_measure (reuse_bootstrap_moment_measurable 2 0).aestronglyMeasurable
      hpinmap.aemeasurable).mp (reuse_bootstrap_moment_integrable _ 2 0)
  · exact ae_of_all _ (fun z => marked_replica_product_le _ _)


def markedOriginalLimit (p : ℝ) : ℝ :=
  let r := (1-p)/p
  1+3*r+3*r^2/2

def markedBootstrapLimit (p : ℝ) : ℝ :=
  let r := (1-p)/p
  let s := matchS
  2+2*r/s+2*r+3*r^2/(2*s)

def markedReplicaLimit (p : ℝ) : ℝ :=
  let r := (1-p)/p
  let s := matchS
  1+2*r+s*r/(2-s)+r^2*(4-s)/(2*(2-s))


theorem marked_limit_functions_continuousOn :
    ContinuousOn markedOriginalLimit (Set.Icc (1/4 : ℝ) (3/4)) ∧
    ContinuousOn markedBootstrapLimit (Set.Icc (1/4 : ℝ) (3/4)) ∧
    ContinuousOn markedReplicaLimit (Set.Icc (1/4 : ℝ) (3/4)) := by
  have hratio : ContinuousOn (fun p : ℝ => (1-p)/p) (Set.Icc (1/4 : ℝ) (3/4)) :=
    (continuous_const.sub continuous_id).continuousOn.div continuousOn_id
      (fun p hp => by linarith [hp.1])
  constructor
  · unfold markedOriginalLimit
    exact ((continuousOn_const.add (continuousOn_const.mul hratio)).add
      ((continuousOn_const.mul (hratio.pow 2)).div_const 2))
  constructor
  · unfold markedBootstrapLimit
    exact (((continuousOn_const.add ((continuousOn_const.mul hratio).div_const _)).add
      (continuousOn_const.mul hratio)).add
      ((continuousOn_const.mul (hratio.pow 2)).div_const _))
  · unfold markedReplicaLimit
    exact (((continuousOn_const.add (continuousOn_const.mul hratio)).add
      ((continuousOn_const.mul hratio).div_const _)).add
      (((hratio.pow 2).mul continuousOn_const).div_const _))


/-- The three exact pinned second-moment limits in the actual finite experiment. -/
theorem pinned_cell_second_moments (p : ℝ)
  (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
  let r := (1-p)/p
  let s := matchS
  Tendsto (fun n => mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2))
    atTop (nhds (1+3*r+3*r^2/2)) ∧
  Tendsto (fun n => mean (MatchProduct n) (fun z =>
    mean (UniformResampling (n+1)) (fun a => (U (pin n p z) a 0)^2)))
    atTop (nhds (2+2*r/s+2*r+3*r^2/(2*s))) ∧
  Tendsto (fun n => mean (MatchProduct n) (fun z =>
    mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b =>
        U (pin n p z) a 0 * U (pin n p z) b 0))))
    atTop (nhds (1+2*r+s*r/(2-s)+r^2*(4-s)/(2*(2-s)))) := by
  dsimp only
  exact ⟨marked_pinned_original_second_limit p hp,
    marked_pinned_bootstrap_second_limit p hp,marked_pinned_replica_second_limit p hp⟩

end AronowAudit.P001.TailA
