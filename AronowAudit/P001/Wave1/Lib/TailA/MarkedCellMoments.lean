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

/-! Pinned matching-cell moment integrands and finite-window calculations. -/

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

theorem marked_pinned_integrands_measurable (n : ℕ) :
    Measurable (fun p : ℝ => mean (MatchProduct n)
      (fun z => (W (pin n p z) 0)^2)) ∧
    Measurable (fun p : ℝ => mean (MatchProduct n) (fun z =>
      mean (UniformResampling (n+1)) (fun a => (U (pin n p z) a 0)^2))) ∧
    Measurable (fun p : ℝ => mean (MatchProduct n) (fun z =>
      mean (UniformResampling (n+1)) (fun a =>
        mean (UniformResampling (n+1)) (fun b =>
          U (pin n p z) a 0 * U (pin n p z) b 0)))) := by
  refine ⟨matching_pinned_W_moment_measurable n 2, ?_, ?_⟩
  · apply matching_pinned_integral_measurable n
      (f := fun z => mean (UniformResampling (n+1)) (fun a => (U z a 0)^2))
    exact marked_resampling_average_measurable _ _
      (fun a => (matching_U_measurable a 0).pow_const 2)
  · apply matching_pinned_integral_measurable n
      (f := fun z => mean (UniformResampling (n+1)) (fun a =>
        mean (UniformResampling (n+1)) (fun b => U z a 0 * U z b 0)))
    apply marked_resampling_average_measurable (n+1)
    intro a
    apply marked_resampling_average_measurable (n+1)
    intro b
    exact (matching_U_measurable a 0).mul (matching_U_measurable b 0)

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

theorem marked_tail_square_le {x K : ℝ} (hK : 0 < K) (hx : K ≤ x) :
    x^2 ≤ x^4/K^2 := by
  have hKx : K^2 ≤ x^2 := pow_le_pow_left₀ hK.le hx 2
  apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hKx (sq_nonneg x)]

/-- Explicit square-truncation error, suitable for removing the weight cutoff. -/
theorem marked_square_truncation_error {x K : ℝ} (hx : 0 ≤ x) (hK : 0 < K) :
    0 ≤ x^2-(min x K)^2 ∧ x^2-(min x K)^2 ≤ x^4/K^2 := by
  by_cases hxK : x ≤ K
  · rw [min_eq_left hxK,sub_self]
    exact ⟨le_rfl,by positivity⟩
  · have hKx := le_of_not_ge hxK
    rw [min_eq_right hKx]
    refine ⟨?_,?_⟩
    · have h := pow_le_pow_left₀ hK.le hKx 2
      linarith
    · have h := marked_tail_square_le hK hKx
      nlinarith [sq_nonneg K]

/-- Truncate both replicas without replacing their shared original-label environment. -/
theorem marked_product_truncation_error {x y K : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hK : 0 < K) :
    0 ≤ x*y-min x K*min y K ∧
      x*y-min x K*min y K ≤ (x^4+y^4)/K^2 := by
  have hminx : 0 ≤ min x K := le_min hx hK.le
  have hminy : 0 ≤ min y K := le_min hy hK.le
  have hprod : min x K*min y K ≤ x*y :=
    mul_le_mul (min_le_left x K) (min_le_left y K) hminy hx
  refine ⟨sub_nonneg.mpr hprod,?_⟩
  by_cases hsmall : x ≤ K ∧ y ≤ K
  · rw [min_eq_left hsmall.1,min_eq_left hsmall.2,sub_self]
    positivity
  have hlarge : K ≤ max x y := by
    by_contra h
    have h' := lt_of_not_ge h
    exact hsmall ⟨(le_max_left x y).trans h'.le,(le_max_right x y).trans h'.le⟩
  have hxy : x*y ≤ (max x y)^2 := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      nlinarith [mul_le_mul_of_nonneg_right h hy]
    · rw [max_eq_left h]
      nlinarith [mul_le_mul_of_nonneg_left h hx]
  have hpow : (max x y)^4 ≤ x^4+y^4 := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      nlinarith [pow_nonneg hx 4]
    · rw [max_eq_left h]
      nlinarith [pow_nonneg hy 4]
  have htail := marked_tail_square_le hK hlarge
  have hdiv := div_le_div_of_nonneg_right hpow (sq_nonneg K)
  nlinarith [mul_nonneg hminx hminy]

/-- The required fourth moments give quantitative removal of the two weight cutoffs. -/
theorem marked_pinned_square_truncation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ),
      p ∈ Set.Icc (1/4 : ℝ) (3/4) → ∀ K : ℝ, 0 < K →
      mean (MatchProduct n) (fun z =>
        (W (pin n p z) 0)^2-(min (W (pin n p z) 0) K)^2) ≤ C/K^2 ∧
      mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a =>
        (U (pin n p z) a 0)^2-(min (U (pin n p z) a 0) K)^2)) ≤ C/K^2 := by
  obtain ⟨C,hC,_,hpin⟩ := uniform_reuse_fourth_moments
  refine ⟨C,hC,fun n p hp K hK => ?_⟩
  have hpinmap := reuse_pin_map_measurable n p
  have hiW : Integrable (fun z => (W (pin n p z) 0)^4) (MatchProduct n) :=
    (integrable_map_measure ((matching_W_measurable 0).pow_const 4).aestronglyMeasurable
      hpinmap.aemeasurable).mp (reuse_W_moment_integrable _ 0 4)
  have hiU : Integrable (fun z => mean (UniformResampling (n+1))
      (fun a => (U (pin n p z) a 0)^4)) (MatchProduct n) :=
    (integrable_map_measure (reuse_bootstrap_moment_measurable 4 0).aestronglyMeasurable
      hpinmap.aemeasurable).mp (reuse_bootstrap_moment_integrable _ 4 0)
  have hW0 (z) : 0 ≤ W (pin n p z) 0 :=
    (matching_weight_bounds _ _ _).1
  have hU0 (z) (a) : 0 ≤ U (pin n p z) a 0 := reuse_bootstrap_nonneg _ _ _ _
  constructor
  · calc
      _ ≤ ∫ z, (W (pin n p z) 0)^4/K^2 ∂MatchProduct n := by
        exact integral_mono_of_nonneg
          (ae_of_all _ (fun z => (marked_square_truncation_error (hW0 z) hK).1))
          (hiW.div_const _)
          (ae_of_all _ (fun z => (marked_square_truncation_error (hW0 z) hK).2))
      _ = mean (MatchProduct n) (fun z => (W (pin n p z) 0)^4)/K^2 := integral_div _ _
      _ ≤ _ := div_le_div_of_nonneg_right (hpin n p hp).1 (sq_nonneg K)
  · calc
      _ ≤ ∫ z, mean (UniformResampling (n+1))
          (fun a => (U (pin n p z) a 0)^4)/K^2 ∂MatchProduct n := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun z => integral_nonneg (fun a =>
            (marked_square_truncation_error (hU0 z a) hK).1))
        · exact hiU.div_const _
        · apply ae_of_all
          intro z
          change (∫ a, (U (pin n p z) a 0)^2-(min (U (pin n p z) a 0) K)^2
              ∂UniformResampling (n+1)) ≤
            (∫ a, (U (pin n p z) a 0)^4 ∂UniformResampling (n+1))/K^2
          rw [← integral_div]
          exact integral_mono_of_nonneg
            (ae_of_all _ (fun a => (marked_square_truncation_error (hU0 z a) hK).1))
            Integrable.of_finite
            (ae_of_all _ (fun a => (marked_square_truncation_error (hU0 z a) hK).2))
      _ = mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
          (fun a => (U (pin n p z) a 0)^4))/K^2 := integral_div _ _
      _ ≤ _ := div_le_div_of_nonneg_right (hpin n p hp).2 (sq_nonneg K)

theorem marked_replica_fourth_sum (n : ℕ) (f : (Fin n → Fin n) → ℝ) (K : ℝ) :
    mean (UniformResampling n) (fun a => mean (UniformResampling n)
      (fun b => ((f a)^4+(f b)^4)/K^2)) =
        2*mean (UniformResampling n) (fun a => (f a)^4)/K^2 := by
  have hi (a) : mean (UniformResampling n) (fun b => ((f a)^4+(f b)^4)/K^2) =
      ((f a)^4+mean (UniformResampling n) (fun b => (f b)^4))/K^2 := by
    rw [mean,integral_div,integral_add (f := fun _ => (f a)^4)
      (g := fun b => (f b)^4) Integrable.of_finite Integrable.of_finite,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul,mean]
  simp only [hi]
  rw [mean,integral_div,integral_add (f := fun a => (f a)^4)
    (g := fun _ => mean (UniformResampling n) (fun a => (f a)^4))
    Integrable.of_finite Integrable.of_finite,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul,mean]
  ring

theorem marked_pinned_product_truncation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ),
      p ∈ Set.Icc (1/4 : ℝ) (3/4) → ∀ K : ℝ, 0 < K →
      mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a =>
        mean (UniformResampling (n+1)) (fun b =>
          U (pin n p z) a 0 * U (pin n p z) b 0 -
            min (U (pin n p z) a 0) K * min (U (pin n p z) b 0) K))) ≤
        2*C/K^2 := by
  obtain ⟨C,hC,_,hpin⟩ := uniform_reuse_fourth_moments
  refine ⟨C,hC,fun n p hp K hK => ?_⟩
  have hpinmap := reuse_pin_map_measurable n p
  have hiU : Integrable (fun z => mean (UniformResampling (n+1))
      (fun a => (U (pin n p z) a 0)^4)) (MatchProduct n) :=
    (integrable_map_measure (reuse_bootstrap_moment_measurable 4 0).aestronglyMeasurable
      hpinmap.aemeasurable).mp (reuse_bootstrap_moment_integrable _ 4 0)
  have hU0 (z) (a) : 0 ≤ U (pin n p z) a 0 := reuse_bootstrap_nonneg _ _ _ _
  calc
    _ ≤ ∫ z, 2*mean (UniformResampling (n+1))
        (fun a => (U (pin n p z) a 0)^4)/K^2 ∂MatchProduct n := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun z => integral_nonneg (fun a => integral_nonneg (fun b =>
          (marked_product_truncation_error (hU0 z a) (hU0 z b) hK).1)))
      · exact (hiU.const_mul 2).div_const _
      · apply ae_of_all
        intro z
        change mean (UniformResampling (n+1)) (fun a =>
            mean (UniformResampling (n+1)) (fun b =>
              U (pin n p z) a 0 * U (pin n p z) b 0 -
                min (U (pin n p z) a 0) K * min (U (pin n p z) b 0) K)) ≤
          2*mean (UniformResampling (n+1)) (fun a => (U (pin n p z) a 0)^4)/K^2
        rw [← marked_replica_fourth_sum (n+1) (fun a => U (pin n p z) a 0) K]
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro a
        exact integral_mono Integrable.of_finite Integrable.of_finite
          (fun b => (marked_product_truncation_error (hU0 z a) (hU0 z b) hK).2)
    _ = 2*mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
        (fun a => (U (pin n p z) a 0)^4))/K^2 := by
      rw [integral_div,integral_const_mul]
      rfl
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpin n p hp).2 (by norm_num)) (sq_nonneg K)

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

theorem marked_limit_functions_measurable :
    Measurable markedOriginalLimit ∧ Measurable markedBootstrapLimit ∧
      Measurable markedReplicaLimit := by
  unfold markedOriginalLimit markedBootstrapLimit markedReplicaLimit
  constructor
  · fun_prop
  constructor <;> fun_prop

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

/-- The candidate limiting integrands themselves have a common bounded envelope. -/
theorem marked_limit_functions_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Set.Icc (1/4 : ℝ) (3/4),
      |markedOriginalLimit p| ≤ C ∧ |markedBootstrapLimit p| ≤ C ∧
        |markedReplicaLimit p| ≤ C := by
  obtain ⟨hO,hB,hR⟩ := marked_limit_functions_continuousOn
  have henv := (hO.abs.add hB.abs).add hR.abs
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image henv
  refine ⟨max C 0+1,by positivity,fun p hp => ?_⟩
  have h := hC (Set.mem_image_of_mem _ hp)
  change |markedOriginalLimit p|+|markedBootstrapLimit p|+|markedReplicaLimit p| ≤ C at h
  have hmax := le_max_left C 0
  have ho := abs_nonneg (markedOriginalLimit p)
  have hb := abs_nonneg (markedBootstrapLimit p)
  have hr := abs_nonneg (markedReplicaLimit p)
  exact ⟨by linarith,by linarith,by linarith⟩

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

/-- Compile-time check of the unchanged planned component type. -/
example (p : ℝ)
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
    atTop (nhds (1+2*r+s*r/(2-s)+r^2*(4-s)/(2*(2-s)))) := pinned_cell_second_moments p hp

end AronowAudit.P001.TailA
