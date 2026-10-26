import AronowAudit.P018.P018_Audit
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! P018-T2, P018-T20 and P018-T22: conditional moments, moment convergence, and Gaussian simulation. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## P018-T2: conditional uncentered moments -/

private instance cmc_sample_probability {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) [IsProbabilityMeasure K.μ] :
    IsProbabilityMeasure (unitSampleLaw K N) := by
  unfold unitSampleLaw
  infer_instance

private theorem cmc_endpoints_ne {N : ℕ} (d : Dyad N) : firstUnit d ≠ secondUnit d := by
  apply ne_of_lt
  exact Finset.min'_lt_max'_of_card (s := members d) (by rw [members_card]; norm_num)

private theorem cmc_pair_preserving {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) :
    MeasurePreserving (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d)))
      (unitSampleLaw K N) (K.μ.prod K.μ) := by
  letI : IsProbabilityMeasure K.μ := hK.1
  have hind : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (unitSampleLaw K N) := iIndepFun_pi (fun _ => aemeasurable_id)
  refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _), ?_⟩
  rw [(hind.indepFun (cmc_endpoints_ne d)).map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable]
  simp only [unitSampleLaw,
    (measurePreserving_eval (fun _ : Fin N => K.μ) (firstUnit d)).map_eq,
    (measurePreserving_eval (fun _ : Fin N => K.μ) (secondUnit d)).map_eq]

private theorem cmc_design_measurable {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) : Measurable (@design U _ k N K) := by
  apply measurable_pi_lambda
  intro d
  have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  simpa only [Function.comp_def, design] using hK.2.1.comp hp

private theorem cmc_epsilon_measurable {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d : Dyad N) :
    Measurable (fun ω : Fin N → U => epsilon K ω d) := by
  have hp : Measurable (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hY : Measurable (fun ω : Fin N → U => response K ω d) := by
    simpa only [Function.comp_def, response] using hK.2.2.1.comp hp
  have hX := cmc_design_measurable (N := N) K hK
  change Measurable (fun ω => response K ω d -
    ∑ a : Fin k, design K ω d a * populationBeta K a)
  exact hY.sub (Finset.measurable_sum _ (fun a _ =>
    ((measurable_pi_apply a).comp ((measurable_pi_apply d).comp hX)).mul_const _))

/-- A common deterministic bound, transported from the two-unit law. -/
private theorem cmc_bounds {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Dyad N, ∀ᵐ ω ∂ unitSampleLaw K N,
      (∀ a, |design K ω d a| ≤ C) ∧ |epsilon K ω d| ≤ C := by
  classical
  obtain ⟨B, hB, hb⟩ := hK.2.2.2.2.1
  let E : ℝ := B + ∑ a : Fin k, B * |populationBeta K a|
  have hE : 0 ≤ E := add_nonneg hB (Finset.sum_nonneg (fun _ _ =>
    mul_nonneg hB (abs_nonneg _)))
  refine ⟨B + E, add_nonneg hB hE, ?_⟩
  intro d
  have hd := (cmc_pair_preserving K hK d).quasiMeasurePreserving.tendsto_ae hb
  filter_upwards [hd] with ω hω
  have hx (a : Fin k) : |design K ω d a| ≤ B := by
    exact (norm_le_pi_norm (design K ω d) a).trans hω.1
  constructor
  · intro a
    exact (hx a).trans (le_add_of_nonneg_right hE)
  · have he : |epsilon K ω d| ≤ E := by
      calc
        _ ≤ |response K ω d| + |∑ a : Fin k,
            design K ω d a * populationBeta K a| := abs_sub _ _
        _ ≤ B + ∑ a : Fin k, |design K ω d a * populationBeta K a| :=
          add_le_add hω.2 (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ E := by
          apply add_le_add (le_refl B)
          apply Finset.sum_le_sum
          intro a ha
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hx a) (abs_nonneg _)
    exact he.trans (le_add_of_nonneg_left hB)

private theorem cmc_integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ᵐ ω ∂ P, |f ω| ≤ B) : Integrable f P := by
  apply (MemLp.of_bound hf.aestronglyMeasurable B hb : MemLp f 2 P).integrable
  norm_num

private theorem cmc_uncentered_entry {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (d f : Dyad N) (a b : Fin k) :
    (∫ ω, (epsilon K ω d * epsilon K ω f) *
        (design K ω d a * design K ω f b) ∂ unitSampleLaw K N) =
      ∫ ω, (MeasureTheory.condExp (designSigma K) (unitSampleLaw K N)
        (fun w => epsilon K w d * epsilon K w f) ω) *
        (design K ω d a * design K ω f b) ∂ unitSampleLaw K N := by
  letI : IsProbabilityMeasure K.μ := hK.1
  let P := unitSampleLaw K N
  let A : (Fin N → U) → ℝ := fun ω => design K ω d a * design K ω f b
  let Z : (Fin N → U) → ℝ := fun ω => epsilon K ω d * epsilon K ω f
  have hm : @designSigma U _ k N K ≤ (inferInstance : MeasurableSpace (Fin N → U)) := (cmc_design_measurable K hK).comap_le
  have hXF : @Measurable (Fin N → U) (Dyad N → Vec k) (designSigma K) inferInstance (design K) :=
    comap_measurable (design K)
  have hAF : StronglyMeasurable[designSigma K] A :=
    (((measurable_pi_apply a).comp ((measurable_pi_apply d).comp hXF)).mul
      ((measurable_pi_apply b).comp ((measurable_pi_apply f).comp hXF))).stronglyMeasurable
  have hA : Measurable A := hAF.measurable.mono hm le_rfl
  have hZ : Measurable Z := (cmc_epsilon_measurable K hK d).mul
    (cmc_epsilon_measurable K hK f)
  obtain ⟨C, hC, hb⟩ := cmc_bounds (N := N) K hK
  have hZi : Integrable Z P := by
    apply cmc_integrable_bounded P Z hZ (C * C)
    filter_upwards [hb d, hb f] with ω hd hf
    exact (abs_mul _ _).le.trans (mul_le_mul hd.2 hf.2 (abs_nonneg _) hC)
  have hAZi : Integrable (A * Z) P := by
    apply cmc_integrable_bounded P (A * Z) (hA.mul hZ) ((C*C)*(C*C))
    filter_upwards [hb d, hb f] with ω hd hf
    change |(design K ω d a * design K ω f b) *
      (epsilon K ω d * epsilon K ω f)| ≤ _
    rw [abs_mul, abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul (hd.1 a) (hf.1 b) (abs_nonneg _) hC)
      (mul_le_mul hd.2 hf.2 (abs_nonneg _) hC)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hC hC)
  have hpull := condExp_mul_of_stronglyMeasurable_left hAF hAZi hZi
  have hi : (∫ ω, A ω * Z ω ∂ P) =
      ∫ ω, A ω * (MeasureTheory.condExp (designSigma K) P Z ω) ∂ P := by
    change (∫ ω, (A * Z) ω ∂ P) = _
    rw [← integral_condExp hm (μ := P) (f := A * Z)]
    exact integral_congr_ae hpull
  simpa only [A, Z, P, mul_comm] using hi

private theorem cmc_zero_covariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (F : Ω → Vec k) (hF : F =ᵐ[P] 0) : varMat P F = 0 := by
  ext a b
  have ha : (fun ω => F ω a) =ᵐ[P] 0 := hF.mono (fun ω hω => congrFun hω a)
  have hb : (fun ω => F ω b) =ᵐ[P] 0 := hF.mono (fun ω hω => congrFun hω b)
  have hia : (∫ ω, F ω a ∂ P) = 0 := by
    simpa using integral_congr_ae ha
  have hib : (∫ ω, F ω b ∂ P) = 0 := by
    simpa using integral_congr_ae hb
  change (∫ ω, (F ω a - ∫ w, F w a ∂ P) *
    (F ω b - ∫ w, F w b ∂ P) ∂ P) = 0
  rw [hia, hib]
  calc
    _ = ∫ _ : Ω, (0 : ℝ) ∂ P := by
      apply integral_congr_ae
      filter_upwards [ha, hb] with ω hωa hωb
      simp [hωa, hωb]
    _ = 0 := by simp only [integral_zero]

theorem conditional_moment_correction_proof {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (hK : Standing K) (hN : 2 ≤ N) :
    correctedSigma K N = (∑ d : Dyad N, ∑ f : Dyad N,
      if overlap d f then meanMat (unitSampleLaw K N) (fun ω =>
        (MeasureTheory.condExp (designSigma K) (unitSampleLaw K N)
          (fun w => epsilon K w d*epsilon K w f) ω) •
          outer (design K ω d) (design K ω f)) else 0) ∧
    ((∀ d : Dyad N, conditionalResidualMean K d =ᵐ[unitSampleLaw K N] 0) →
      varMat (unitSampleLaw K N) (fun ω => ∑ d : Dyad N,
        score (design K ω d) (conditionalResidualMean K d ω)) = 0) := by
  classical
  letI : IsProbabilityMeasure K.μ := hK.1
  obtain ⟨C, hC, hb⟩ := cmc_bounds (N := N) K hK
  have hX := cmc_design_measurable (N := N) K hK
  have hi (d f : Dyad N) (a b : Fin k) : Integrable
      (fun ω => outer (score (design K ω d) (epsilon K ω d))
        (score (design K ω f) (epsilon K ω f)) a b) (unitSampleLaw K N) := by
    apply cmc_integrable_bounded _ _
      (((cmc_epsilon_measurable K hK d).mul
        ((measurable_pi_apply a).comp ((measurable_pi_apply d).comp hX))).mul
       ((cmc_epsilon_measurable K hK f).mul
        ((measurable_pi_apply b).comp ((measurable_pi_apply f).comp hX))))
      ((C*C)*(C*C))
    filter_upwards [hb d, hb f] with ω hd hf
    change |(epsilon K ω d * design K ω d a) * (epsilon K ω f * design K ω f b)| ≤ _
    rw [abs_mul, abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul hd.2 (hd.1 a) (abs_nonneg _) hC)
      (mul_le_mul hf.2 (hf.1 b) (abs_nonneg _) hC)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hC hC)
  constructor
  · ext a b
    simp only [correctedSigma, meanMat, meat, Matrix.sum_apply, Finset.sum_apply,
      matrix_ite_apply, Matrix.zero_apply]
    rw [integral_finsetSum univ (fun d _ => integrable_finset_sum univ
      (fun f _ => by
        by_cases h : (members d ∩ members f).Nonempty
        · simpa only [h, if_true] using hi d f a b
        · simp only [h, if_false]
          exact integrable_zero _ _ _))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [integral_finsetSum univ (fun f _ => by
      by_cases h : (members d ∩ members f).Nonempty <;> simp only [h, if_true, if_false]
      · exact hi d f a b
      · exact integrable_zero _ _ _)]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases h : (members d ∩ members f).Nonempty
    · have ho : overlap d f := h
      rw [if_pos ho]
      simp only [if_pos h, meanMat, Matrix.smul_apply, smul_eq_mul, outer, score,
        Pi.smul_apply]
      convert cmc_uncentered_entry K hK d f a b using 1 <;>
        congr 1 <;> funext ω <;> ring
    · have ho : ¬ overlap d f := h
      rw [if_neg ho]
      simp only [if_neg h, integral_zero, Matrix.zero_apply]
  · intro hz
    apply cmc_zero_covariance
    have hall : ∀ᵐ ω ∂ unitSampleLaw K N, ∀ d : Dyad N,
        conditionalResidualMean K d ω = 0 := by
      simpa only [Pi.zero_apply] using (ae_all_iff.mpr hz)
    filter_upwards [hall] with ω hω
    simp only [hω, score, zero_smul, Finset.sum_const_zero, Pi.zero_apply]

/-! ## P018-T20: weak convergence and UI squares -/

private def vui_q {k : ℕ} (x : Vec k) : ℝ := ∑ a, (x a)^2

private theorem vui_q_continuous {k : ℕ} : Continuous (@vui_q k) := by
  exact continuous_finset_sum _ (fun a _ => (continuous_apply a).pow 2)

private theorem vui_q_nonneg {k : ℕ} (x : Vec k) : 0 ≤ vui_q x :=
  Finset.sum_nonneg (fun a _ => sq_nonneg (x a))

private theorem vui_sq_le_q {k : ℕ} (x : Vec k) (a : Fin k) : (x a)^2 ≤ vui_q x := by
  exact Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)

private def vui_tail {k : ℕ} (C : ℝ) (x : Vec k) : ℝ :=
  if C < vui_q x then vui_q x else 0

private theorem vui_tail_measurable {k : ℕ} (C : ℝ) : Measurable (@vui_tail k C) := by
  exact Measurable.ite (measurableSet_lt measurable_const vui_q_continuous.measurable)
    vui_q_continuous.measurable measurable_const

private theorem vui_tail_bounds {k : ℕ} (C : ℝ) (x : Vec k) :
    0 ≤ vui_tail C x ∧ |vui_tail C x| ≤ vui_q x := by
  by_cases h : C < vui_q x <;>
    simp [vui_tail, h, abs_of_nonneg (vui_q_nonneg x), vui_q_nonneg]

private theorem vui_tail_antitone {k : ℕ} {B C : ℝ} (hBC : B ≤ C) (x : Vec k) :
    vui_tail C x ≤ vui_tail B x := by
  by_cases hc : C < vui_q x
  · simp [vui_tail, hc, lt_of_le_of_lt hBC hc]
  · simp only [vui_tail, hc, if_false]
    exact (vui_tail_bounds B x).1

private theorem vui_q_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Vec k) (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 P) :
    Integrable (fun ω => vui_q (X ω)) P :=
  integrable_finset_sum univ (fun a _ => (hL2 a).integrable_sq)

private theorem vui_tail_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Vec k) (hX : AEMeasurable X P)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 P) (C : ℝ) :
    Integrable (fun ω => vui_tail C (X ω)) P := by
  apply (vui_q_integrable P X hL2).mono'
    (((vui_tail_measurable C).aemeasurable.comp_aemeasurable hX).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => (vui_tail_bounds C (X ω)).2)

private def vui_clip (C y : ℝ) : ℝ := min C (max (-C) y)

private theorem vui_clip_abs {C : ℝ} (hC : 0 ≤ C) (y : ℝ) : |vui_clip C y| ≤ C := by
  rw [abs_le]
  exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩

private theorem vui_clip_eq {C y : ℝ} (hy : |y| ≤ C) : vui_clip C y = y := by
  unfold vui_clip
  rw [max_eq_right (abs_le.mp hy).1, min_eq_right (abs_le.mp hy).2]

private theorem vui_clip_error {C y : ℝ} (hC : 0 ≤ C) :
    |y - vui_clip C y| ≤ |y| := by
  by_cases hu : C < y
  · have hc : vui_clip C y = C := by
      simp [vui_clip, max_eq_right (by linarith : -C ≤ y), min_eq_left hu.le]
    have hd : 0 ≤ y - C := by linarith
    have hy : 0 ≤ y := by linarith
    rw [hc, abs_of_nonneg hd, abs_of_nonneg hy]
    linarith
  · by_cases hl : y < -C
    · have hc : vui_clip C y = -C := by
        simp [vui_clip, max_eq_left hl.le, min_eq_right (by linarith : -C ≤ C)]
      have hd : y - (-C) ≤ 0 := by linarith
      have hy : y ≤ 0 := by linarith
      rw [hc, abs_of_nonpos hd, abs_of_nonpos hy]
      linarith
    · have hbounds : |y| ≤ C := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [vui_clip_eq hbounds, sub_self, abs_zero]
      exact abs_nonneg _

/-- The same scalar clipping estimate works for both kinds of moments. -/
private theorem vui_clip_tail {k : ℕ} (F : Vec k → ℝ)
    (hF : ∀ x, |F x| ≤ max 1 (vui_q x)) {C : ℝ} (hC : 1 ≤ C) (x : Vec k) :
    |F x - vui_clip C (F x)| ≤ vui_tail C x := by
  by_cases hq : C < vui_q x
  · rw [vui_tail, if_pos hq]
    exact (vui_clip_error (C := C) (y := F x) (by linarith)).trans
      ((hF x).trans (max_le (by linarith) le_rfl))
  · have hf : |F x| ≤ C := (hF x).trans (max_le hC (le_of_not_gt hq))
    simp [vui_tail, hq, vui_clip_eq hf]

private def vui_bounded_test {k : ℕ} (F : Vec k → ℝ) (hF : Continuous F)
    (C : ℝ) (hC : 0 ≤ C) : Vec k →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => vui_clip C (F x), continuous_const.min ((continuous_const).max hF)⟩
    (2*C) (by
      intro x y
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by
        have hx := vui_clip_abs hC (F x)
        have hy := vui_clip_abs hC (F y)
        change |vui_clip C (F x)| + |vui_clip C (F y)| ≤ 2*C
        linarith))

/-- The limiting law has vanishing square-radius tails, by ordinary DCT. -/
private theorem vui_limit_tail {k : ℕ} (ν : Measure (Vec k))
    (hL2 : ∀ a, MemLp (fun x : Vec k => x a) 2 ν) :
    Tendsto (fun n : ℕ => ∫ x, vui_tail (n : ℝ) x ∂ ν) atTop (𝓝 0) := by
  have hi := vui_q_integrable ν id hL2
  have ht : Tendsto (fun n : ℕ => ∫ x, vui_tail (n : ℝ) x ∂ ν)
      atTop (𝓝 (∫ _ : Vec k, (0 : ℝ) ∂ ν)) := by
    apply tendsto_integral_of_dominated_convergence vui_q
      (fun n => (vui_tail_measurable (n : ℝ)).aestronglyMeasurable) hi
    · intro n
      exact Filter.Eventually.of_forall (fun x => (vui_tail_bounds (n : ℝ) x).2)
    · apply Filter.Eventually.of_forall
      intro x
      apply tendsto_const_nhds.congr'
      have he : ∀ᶠ n : ℕ in atTop, vui_q x ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (vui_q x))
      filter_upwards [he] with n hn
      simp [vui_tail, not_lt.mpr hn]
  simpa only [integral_zero] using ht

private theorem vui_truncation_integral_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Vec k)
    (hX : AEMeasurable X P) (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 P)
    (F : Vec k → ℝ) (hFc : Continuous F) (hFi : Integrable (fun ω => F (X ω)) P)
    (hF : ∀ x, |F x| ≤ max 1 (vui_q x)) (C : ℝ) (hC : 1 ≤ C) :
    |(∫ ω, F (X ω) ∂ P) -
      ∫ ω, vui_bounded_test F hFc C (by linarith) (X ω) ∂ P| ≤
      ∫ ω, vui_tail C (X ω) ∂ P := by
  let g := vui_bounded_test F hFc C (by linarith)
  have hgi : Integrable (fun ω => g (X ω)) P := by
    apply (integrable_const C).mono'
      (g.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => vui_clip_abs (by linarith) (F (X ω)))
  rw [← integral_sub hFi hgi]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (vui_tail_integrable P X hX hL2 C)
  exact Filter.Eventually.of_forall (fun ω => vui_clip_tail F hF hC (X ω))

/-- A scalar weak-moment transfer. -/
private theorem vui_moment {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {k : ℕ} (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (ξ : ∀ N, Ω N → Vec k) (ν : Measure (Vec k))
    (hweak : weakLimit μ ξ ν) (hui : uiSquares μ ξ)
    (hL2 : ∀ a, MemLp (fun x : Vec k => x a) 2 ν)
    (F : Vec k → ℝ) (hFc : Continuous F)
    (hFi : ∀ N, Integrable (fun ω => F (ξ N ω)) (μ N))
    (hFν : Integrable F ν) (hF : ∀ x, |F x| ≤ max 1 (vui_q x)) :
    Tendsto (fun N => ∫ ω, F (ξ N ω) ∂ μ N) atTop (𝓝 (∫ x, F x ∂ ν)) := by
  letI : IsProbabilityMeasure ν := hweak.2.1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B, hB, hBt⟩ := hui.2 (ε/3) (by linarith)
  have hνsmall : ∀ᶠ n : ℕ in atTop, (∫ x, vui_tail (n : ℝ) x ∂ ν) < ε/3 :=
    (vui_limit_tail ν hL2).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε/3))
  obtain ⟨n, hn⟩ := hνsmall.exists
  let C : ℝ := max 1 (max B (n : ℝ))
  have hC : 1 ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B (n : ℝ)).trans (le_max_right _ _)
  have hnC : (n : ℝ) ≤ C := (le_max_right B (n : ℝ)).trans (le_max_right _ _)
  let g := vui_bounded_test F hFc C (by linarith)
  have hgt := Metric.tendsto_nhds.mp (hweak.2.2 g) (ε/3) (by linarith)
  filter_upwards [hgt] with N hN
  letI : IsProbabilityMeasure (μ N) := hμ N
  have hs : |(∫ ω, F (ξ N ω) ∂ μ N) - ∫ ω, g (ξ N ω) ∂ μ N| < ε/3 := by
    apply lt_of_le_of_lt (vui_truncation_integral_bound (μ N) (ξ N)
      (hweak.1 N) (hui.1 N) F hFc (hFi N) hF C hC)
    apply lt_of_le_of_lt (integral_mono
      (vui_tail_integrable (μ N) (ξ N) (hweak.1 N) (hui.1 N) C)
      (vui_tail_integrable (μ N) (ξ N) (hweak.1 N) (hui.1 N) B)
      (fun ω => vui_tail_antitone hBC (ξ N ω)))
    exact hBt N
  have hl : |(∫ x, F x ∂ ν) - ∫ x, g x ∂ ν| < ε/3 := by
    apply lt_of_le_of_lt (vui_truncation_integral_bound ν id aemeasurable_id
      hL2 F hFc hFν hF C hC)
    apply lt_of_le_of_lt (integral_mono
      (vui_tail_integrable ν id aemeasurable_id hL2 C)
      (vui_tail_integrable ν id aemeasurable_id hL2 (n : ℝ))
      (fun x => vui_tail_antitone hnC x))
    exact hn
  rw [Real.dist_eq] at hN ⊢
  have ht := abs_sub_le (∫ ω, F (ξ N ω) ∂ μ N)
    (∫ ω, g (ξ N ω) ∂ μ N) (∫ x, F x ∂ ν)
  have hu := abs_sub_le (∫ ω, g (ξ N ω) ∂ μ N) (∫ x, g x ∂ ν) (∫ x, F x ∂ ν)
  rw [abs_sub_comm (∫ x, g x ∂ ν) (∫ x, F x ∂ ν)] at hu
  linarith

private theorem vui_coordinate_bound {k : ℕ} (a : Fin k) (x : Vec k) :
    |x a| ≤ max 1 (vui_q x) := by
  have ha := vui_sq_le_q x a
  by_cases hsmall : |x a| ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : 1 ≤ |x a| := le_of_lt (lt_of_not_ge hsmall)
    have habs : |x a|^2 = (x a)^2 := sq_abs _
    have hsq : |x a| ≤ (x a)^2 := by
      have hmul : 0 ≤ |x a| * (|x a| - 1) :=
        mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hlarge)
      nlinarith
    exact (hsq.trans ha).trans (le_max_right _ _)

private theorem vui_product_bound {k : ℕ} (a b : Fin k) (x : Vec k) :
    |x a * x b| ≤ max 1 (vui_q x) := by
  have ha := vui_sq_le_q x a
  have hb := vui_sq_le_q x b
  have hh : |x a * x b| ≤ vui_q x := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x a| - |x b|), sq_abs (x a), sq_abs (x b)]
  exact hh.trans (le_max_right _ _)

theorem variance_limit_with_UI_proof {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {k : ℕ} (μ : ∀ N : ℕ, Measure (Ω N)) (hμ : ∀ N : ℕ, IsProbabilityMeasure (μ N))
    (ξ : ∀ N : ℕ, Ω N → Vec k) (ν : Measure (Vec k))
    (hweak : weakLimit μ ξ ν) (hui : uiSquares μ ξ)
    (hL2 : ∀ a, MemLp (fun x : Vec k => x a) 2 ν)
    (hzero : meanVec ν id = 0) :
    Tendsto (fun N : ℕ => meanVec (μ N) (ξ N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => varMat (μ N) (ξ N)) atTop (𝓝 (varMat ν id)) := by
  letI : IsProbabilityMeasure ν := hweak.2.1
  have hm (a : Fin k) : Tendsto (fun N => ∫ ω, ξ N ω a ∂ μ N)
      atTop (𝓝 (∫ x, x a ∂ ν)) := by
    apply vui_moment μ hμ ξ ν hweak hui hL2 (fun x => x a) (continuous_apply a)
    · intro N
      letI : IsProbabilityMeasure (μ N) := hμ N
      exact (hui.1 N a).integrable (by norm_num)
    · exact (hL2 a).integrable (by norm_num)
    · exact vui_coordinate_bound a
  have hp (a b : Fin k) : Tendsto (fun N => ∫ ω, ξ N ω a * ξ N ω b ∂ μ N)
      atTop (𝓝 (∫ x, x a * x b ∂ ν)) := by
    apply vui_moment μ hμ ξ ν hweak hui hL2 (fun x => x a * x b)
      ((continuous_apply a).mul (continuous_apply b))
    · intro N
      exact (hui.1 N a).integrable_mul (hui.1 N b)
    · exact (hL2 a).integrable_mul (hL2 b)
    · exact vui_product_bound a b
  constructor
  · apply tendsto_pi_nhds.mpr
    intro a
    have hz : (∫ x, x a ∂ ν) = 0 := congrFun hzero a
    simpa only [meanVec, hz, Pi.zero_apply] using hm a
  · apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    have ht := (hp a b).sub ((hm a).mul (hm b))
    have hcN (N : ℕ) : varMat (μ N) (ξ N) a b =
        (∫ ω, ξ N ω a * ξ N ω b ∂ μ N) -
        (∫ ω, ξ N ω a ∂ μ N) * (∫ ω, ξ N ω b ∂ μ N) := by
      letI : IsProbabilityMeasure (μ N) := hμ N
      exact covariance_eq_sub (hui.1 N a) (hui.1 N b)
    have hcν : varMat ν id a b = (∫ x, x a * x b ∂ ν) -
        (∫ x, x a ∂ ν) * (∫ x, x b ∂ ν) :=
      covariance_eq_sub (hL2 a) (hL2 b)
    simpa only [← hcN, ← hcν] using ht

/-! ## P018-T22: independent Gaussian simulation blocks -/

private instance sdc_probability (N T : ℕ) : IsProbabilityMeasure (simulationLaw N T) := by
  unfold simulationLaw
  infer_instance

private def sdc_errorMap (N T : ℕ) :
    (SimulationIndex N T → ℝ) →L[ℝ] (Dyad N × Fin T → ℝ) :=
  ContinuousLinearMap.pi (fun dt =>
    (∑ i ∈ members dt.1,
      (ContinuousLinearMap.proj (Sum.inr (Sum.inl i)) :
        (SimulationIndex N T → ℝ) →L[ℝ] ℝ)) +
    ContinuousLinearMap.proj (Sum.inr (Sum.inr dt)))

private theorem sdc_errorMap_apply (N T : ℕ) (ω : SimulationIndex N T → ℝ) :
    sdc_errorMap N T ω = fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2 := by
  ext dt
  simp [sdc_errorMap, simulationError]

/-- Transfer standard Gaussianity back from EuclideanSpace to the finite Pi space. -/
private theorem sdc_gaussian_source (N T : ℕ) : IsGaussian (simulationLaw N T) := by
  let e : EuclideanSpace ℝ (SimulationIndex N T) ≃L[ℝ] (SimulationIndex N T → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : SimulationIndex N T => ℝ)
  apply (isGaussian_map_equiv_iff e.symm).mp
  change IsGaussian ((Measure.pi (fun _ : SimulationIndex N T => gaussianReal 0 1)).map
    (WithLp.toLp 2))
  rw [map_pi_eq_stdGaussian]
  infer_instance

private theorem sdc_gaussian_errors (N T : ℕ) :
    IsGaussian ((simulationLaw N T).map (fun ω =>
      fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)) := by
  letI : IsGaussian (simulationLaw N T) := sdc_gaussian_source N T
  have h : (fun ω : SimulationIndex N T → ℝ =>
      fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2) = sdc_errorMap N T :=
    funext (fun ω => (sdc_errorMap_apply N T ω).symm)
  rw [h]
  infer_instance

private theorem sdc_independent_blocks (N T : ℕ) :
    IndepFun (fun ω : SimulationIndex N T → ℝ =>
      fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)
      (fun ω => fun i : Fin N => simulationX ω i) (simulationLaw N T) := by
  classical
  let S : Finset (SimulationIndex N T) :=
    (univ : Finset (Fin N ⊕ (Dyad N × Fin T))).image Sum.inr
  let V : Finset (SimulationIndex N T) := (univ : Finset (Fin N)).image Sum.inl
  have hSV : Disjoint S V := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiV
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiS
    obtain ⟨l, hl, hli⟩ := Finset.mem_image.mp hiV
    exact Sum.inr_ne_inl (hji.trans hli.symm)
  let E : (S → ℝ) → (Dyad N × Fin T → ℝ) := fun z dt =>
    (∑ i ∈ members dt.1, z ⟨Sum.inr (Sum.inl i), by simp [S]⟩) +
      z ⟨Sum.inr (Sum.inr dt), by simp [S]⟩
  let X : (V → ℝ) → (Fin N → ℝ) := fun z i => z ⟨Sum.inl i, by simp [V]⟩
  have hE : Measurable E := by
    apply measurable_pi_lambda
    intro dt
    exact (Finset.measurable_sum (members dt.1) (fun i _ =>
      measurable_pi_apply (⟨Sum.inr (Sum.inl i), by simp [S]⟩ : S))).add
      (measurable_pi_apply (⟨Sum.inr (Sum.inr dt), by simp [S]⟩ : S))
  have hX : Measurable X := measurable_pi_lambda (fun i => measurable_pi_apply _)
  have hind : iIndepFun (fun i : SimulationIndex N T =>
      fun ω : SimulationIndex N T → ℝ => ω i) (simulationLaw N T) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hblocks := hind.indepFun_finset S V hSV (fun i => measurable_pi_apply i)
  have hc := hblocks.comp hE hX
  simpa only [Function.comp_def, E, X, simulationError, simulationX] using hc

private theorem sdc_coord_L2 (N T : ℕ) (i : SimulationIndex N T) :
    MemLp (fun ω : SimulationIndex N T → ℝ => ω i) 2 (simulationLaw N T) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : SimulationIndex N T => gaussianReal 0 1) i)

private theorem sdc_coord_mean (N T : ℕ) (i : SimulationIndex N T) :
    (∫ ω : SimulationIndex N T → ℝ, ω i ∂ simulationLaw N T) = 0 := by
  rw [simulationLaw, integral_eval, integral_id_gaussianReal]

private theorem sdc_coord_cov (N T : ℕ) (i j : SimulationIndex N T) :
    ProbabilityTheory.covariance (fun ω : SimulationIndex N T → ℝ => ω i)
      (fun ω => ω j) (simulationLaw N T) = if i=j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_self (measurable_pi_apply i).aemeasurable]
    have hmap := (measurePreserving_eval
      (fun _ : SimulationIndex N T => gaussianReal 0 1) i).map_eq
    have hv := variance_map (μ := simulationLaw N T) (Y := fun ω => ω i)
      (X := id) aemeasurable_id (measurable_pi_apply i).aemeasurable
    change (Measure.map (fun ω : SimulationIndex N T → ℝ => ω i) (simulationLaw N T)) = gaussianReal 0 1 at hmap
    rw [hmap] at hv
    simpa only [Function.id_comp, variance_id_gaussianReal, NNReal.coe_one] using hv.symm
  · rw [if_neg hij]
    have hind : iIndepFun (fun p : SimulationIndex N T =>
        fun ω : SimulationIndex N T → ℝ => ω p) (simulationLaw N T) :=
      iIndepFun_pi (fun _ => aemeasurable_id)
    exact (hind.indepFun hij).covariance_eq_zero (sdc_coord_L2 N T i) (sdc_coord_L2 N T j)

private theorem sdc_effect_L2 {N T : ℕ} (d : Dyad N) :
    MemLp (fun ω : SimulationIndex N T → ℝ =>
      ∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) 2 (simulationLaw N T) :=
  memLp_finsetSum (members d) (fun i _ => sdc_coord_L2 N T _)


private theorem sdc_error_mean {N T : ℕ} (d : Dyad N) (t : Fin T) :
    (∫ ω : SimulationIndex N T → ℝ, simulationError ω d t ∂ simulationLaw N T) = 0 := by
  simp only [simulationError]
  rw [integral_add ((sdc_effect_L2 d).integrable (by norm_num))
    ((sdc_coord_L2 N T _).integrable (by norm_num))]
  rw [integral_finsetSum (members d) (fun i _ =>
    (sdc_coord_L2 N T _).integrable (by norm_num))]
  simp only [sdc_coord_mean, Finset.sum_const_zero, add_zero]

private theorem sdc_shared_sum {N : ℕ} (d f : Dyad N) :
    (∑ i ∈ members d, ∑ j ∈ members f, (if i=j then (1 : ℝ) else 0)) =
      ((members d ∩ members f).card : ℝ) := by
  classical
  calc
    _ = ∑ i ∈ members d, if i ∈ members f then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem sdc_error_cov {N T : ℕ} (d f : Dyad N) (t u : Fin T) :
    ProbabilityTheory.covariance
      (fun ω : SimulationIndex N T → ℝ => simulationError ω d t)
      (fun ω => simulationError ω f u) (simulationLaw N T) =
      ((members d ∩ members f).card : ℝ) + (if d=f ∧ t=u then 1 else 0) := by
  classical
  let A (q : Dyad N) : (SimulationIndex N T → ℝ) → ℝ :=
    fun ω => ∑ i ∈ members q, ω (Sum.inr (Sum.inl i))
  let Z (q : Dyad N) (v : Fin T) : (SimulationIndex N T → ℝ) → ℝ :=
    fun ω => ω (Sum.inr (Sum.inr (q,v)))
  have hA (q : Dyad N) : MemLp (A q) 2 (simulationLaw N T) := sdc_effect_L2 q
  have hZ (q : Dyad N) (v : Fin T) : MemLp (Z q v) 2 (simulationLaw N T) :=
    sdc_coord_L2 N T _
  have hAA : ProbabilityTheory.covariance (A d) (A f) (simulationLaw N T) =
      ((members d ∩ members f).card : ℝ) := by
    rw [show A d = (fun ω => ∑ i ∈ members d, ω (Sum.inr (Sum.inl i))) from rfl,
      show A f = (fun ω => ∑ i ∈ members f, ω (Sum.inr (Sum.inl i))) from rfl]
    rw [covariance_fun_sum_fun_sum' (fun i _ => sdc_coord_L2 N T _)
      (fun j _ => sdc_coord_L2 N T _)]
    simp only [sdc_coord_cov, Sum.inr.injEq, Sum.inl.injEq]
    exact sdc_shared_sum d f
  have hAZ : ProbabilityTheory.covariance (A d) (Z f u) (simulationLaw N T) = 0 := by
    rw [covariance_fun_sum_left' (fun i _ => sdc_coord_L2 N T _) (hZ f u)]
    simp [Z, sdc_coord_cov]
  have hZA : ProbabilityTheory.covariance (Z d t) (A f) (simulationLaw N T) = 0 := by
    rw [covariance_fun_sum_right' (fun i _ => sdc_coord_L2 N T _) (hZ d t)]
    simp [Z, sdc_coord_cov]
  have hZZ : ProbabilityTheory.covariance (Z d t) (Z f u) (simulationLaw N T) =
      if d=f ∧ t=u then 1 else 0 := by
    simp [Z, sdc_coord_cov, Prod.ext_iff]
  change ProbabilityTheory.covariance (A d + Z d t) (A f + Z f u)
    (simulationLaw N T) = _
  rw [covariance_add_left (hA d) (hZ d t) ((hA f).add (hZ f u)),
    covariance_add_right (hA d) (hA f) (hZ f u),
    covariance_add_right (hZ d t) (hA f) (hZ f u), hAA, hAZ, hZA, hZZ]
  ring

private theorem sdc_conditional_zero {N T : ℕ} (d : Dyad N) (t : Fin T) :
    MeasureTheory.condExp (MeasurableSpace.comap
      (fun ω : SimulationIndex N T → ℝ => fun i : Fin N => simulationX ω i) inferInstance)
      (simulationLaw N T) (fun ω => simulationError ω d t) =ᵐ[simulationLaw N T] 0 := by
  let X : (SimulationIndex N T → ℝ) → (Fin N → ℝ) :=
    fun ω i => simulationX ω i
  let E : (SimulationIndex N T → ℝ) → ℝ := fun ω => simulationError ω d t
  have hX : Measurable X := measurable_pi_lambda (fun i => measurable_pi_apply _)
  have hE : Measurable E := by
    exact (Finset.measurable_sum (members d) (fun i _ =>
      measurable_pi_apply (Sum.inr (Sum.inl i) : SimulationIndex N T))).add
      (measurable_pi_apply (Sum.inr (Sum.inr (d,t)) : SimulationIndex N T))
  have hind : IndepFun E X (simulationLaw N T) :=
    (sdc_independent_blocks N T).comp (measurable_pi_apply (d,t)) measurable_id
  have hmX : MeasurableSpace.comap X inferInstance ≤ (inferInstance : MeasurableSpace (SimulationIndex N T → ℝ)) := hX.comap_le
  have hmE : MeasurableSpace.comap E inferInstance ≤ (inferInstance : MeasurableSpace (SimulationIndex N T → ℝ)) := hE.comap_le
  have hEF : @StronglyMeasurable (SimulationIndex N T → ℝ) ℝ _
      (MeasurableSpace.comap E inferInstance) E :=
    (comap_measurable E).stronglyMeasurable
  have hc := MeasureTheory.condExp_indep_eq hmE hmX hEF hind
  have hz : (∫ ω, E ω ∂ simulationLaw N T) = 0 := sdc_error_mean d t
  filter_upwards [hc] with ω hω
  exact hω.trans hz

theorem simulation_design_correction_proof (N T : ℕ) (hN : 2 ≤ N) (hT : 1 ≤ T) :
    IsGaussian ((simulationLaw N T).map (fun ω =>
      fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)) ∧
    IndepFun (fun ω => fun dt : Dyad N × Fin T => simulationError ω dt.1 dt.2)
      (fun ω => fun i : Fin N => simulationX ω i) (simulationLaw N T) ∧
    (∀ d t, (∫ ω, simulationError ω d t ∂ simulationLaw N T) = 0) ∧
    (∀ d f : Dyad N, ∀ t u : Fin T, ProbabilityTheory.covariance
      (fun ω => simulationError ω d t) (fun ω => simulationError ω f u) (simulationLaw N T) =
        ((members d ∩ members f).card : ℝ) + (if d=f ∧ t=u then 1 else 0)) ∧
    (∀ d t, MeasureTheory.condExp (MeasurableSpace.comap
      (fun ω : SimulationIndex N T → ℝ => fun i : Fin N => simulationX ω i) inferInstance)
      (simulationLaw N T) (fun ω => simulationError ω d t) =ᵐ[simulationLaw N T] 0) := by
  exact ⟨sdc_gaussian_errors N T, sdc_independent_blocks N T,
    fun d t => sdc_error_mean d t, fun d f t u => sdc_error_cov d f t u,
    fun d t => sdc_conditional_zero d t⟩

end AronowAudit.P018.Wave1
