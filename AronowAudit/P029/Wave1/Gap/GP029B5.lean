import AronowAudit.P029.P029_Audit
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
P029-T6: moments of the coded heterogeneous benchmark.
-/

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Bounded support supplies L² membership before the uniform moments are used. -/
lemma hbm_uniform_law_L2_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ)
    (hm : Measurable V) (hlaw : Measure.map V μ = uniformMinusOneOne) :
    MemLp V 2 μ ∧ (∫ ω, V ω ∂μ) = 0 ∧
      (∫ ω, V ω ^ 2 ∂μ) = 1 / 3 ∧ variance V μ = 1 / 3 := by
  have huniform : ∀ᵐ u ∂uniformMinusOneOne, u ∈ Ioo (-1 : ℝ) 1 := by
    exact ae_cond_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo
  have hsupport : ∀ᵐ ω ∂μ, V ω ∈ Ioo (-1 : ℝ) 1 := by
    apply ae_of_ae_map hm.aemeasurable
    rw [hlaw]
    exact huniform
  have hbounded : ∀ᵐ ω ∂μ, V ω ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hsupport] with ω hω
    exact ⟨hω.1.le, hω.2.le⟩
  have hV2 : MemLp V 2 μ :=
    memLp_of_bounded hbounded hm.aestronglyMeasurable 2
  have hmean : (∫ ω, V ω ∂μ) = 0 := by
    calc
      (∫ ω, V ω ∂μ) = ∫ u, u ∂Measure.map V μ :=
        (integral_map_of_stronglyMeasurable hm
          (measurable_id : Measurable (fun u : ℝ => u)).stronglyMeasurable).symm
      _ = ∫ u, u ∂uniformMinusOneOne := by rw [hlaw]
      _ = 0 := uniform_covariate_moments.1
  have hsecond : (∫ ω, V ω ^ 2 ∂μ) = 1 / 3 := by
    calc
      (∫ ω, V ω ^ 2 ∂μ) = ∫ u, u ^ 2 ∂Measure.map V μ :=
        (integral_map_of_stronglyMeasurable hm
          ((measurable_id : Measurable (fun u : ℝ => u)).pow_const 2).stronglyMeasurable).symm
      _ = ∫ u, u ^ 2 ∂uniformMinusOneOne := by rw [hlaw]
      _ = 1 / 3 := uniform_covariate_moments.2
  have hvar : variance V μ = 1 / 3 := by
    rw [variance_eq_sub hV2]
    change (∫ ω, V ω ^ 2 ∂μ) - (∫ ω, V ω ∂μ) ^ 2 = 1 / 3
    rw [hmean, hsecond]
    ring
  exact ⟨hV2, hmean, hsecond, hvar⟩

/-- Flattening the array gives 3n summands of variance 1/3. -/
lemma hbm_flattened_uniform_sum_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Fin 3 → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun ij : Fin n × Fin 3 => X ij.1 ij.2) μ)
    (hlaw : ∀ i j, Measure.map (X i j) μ = uniformMinusOneOne) :
    MemLp (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) 2 μ ∧
      (∫ ω, (∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) ∂μ) = 0 ∧
      variance (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) μ = n := by
  have hcoord := fun (ij : Fin n × Fin 3) =>
    hbm_uniform_law_L2_moments μ (X ij.1 ij.2)
      (hm ij.1 ij.2) (hlaw ij.1 ij.2)
  have hL2 : ∀ ij : Fin n × Fin 3, MemLp (X ij.1 ij.2) 2 μ :=
    fun ij => (hcoord ij).1
  have hsum2 : MemLp (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun ij _ => hL2 ij)
  have hsummean : (∫ ω, (∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ
      (fun ij _ => (hL2 ij).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun ij _ => (hcoord ij).2.1)
  have hpair : Set.Pairwise ((Finset.univ : Finset (Fin n × Fin 3)) : Set (Fin n × Fin 3))
      (fun a b : Fin n × Fin 3 => IndepFun (X a.1 a.2) (X b.1 b.2) μ) := by
    intro a _ b _ hab
    exact hind.indepFun hab
  have hsumvar :
      variance (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) μ = n := by
    calc
      variance (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) μ =
          ∑ ij : Fin n × Fin 3, variance (X ij.1 ij.2) μ := by
        have hsumfun : (∑ ij : Fin n × Fin 3, X ij.1 ij.2) =
            (fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω) := by
          funext ω
          simp only [Finset.sum_apply]
        rw [← hsumfun]
        exact IndepFun.variance_sum (X := fun ij : Fin n × Fin 3 => X ij.1 ij.2)
          (s := Finset.univ) (fun ij _ => hL2 ij) hpair
      _ = ∑ _ij : Fin n × Fin 3, (1 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij _
        exact (hcoord ij).2.2.2
      _ = n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  exact ⟨hsum2, hsummean, hsumvar⟩

/-- The actual code's benchmark, with its constants and three columns expanded. -/
lemma hbm_benchmark_affine_normalization (n : ℕ) (hn : 0 < n)
    (x : Fin n → Fin 3 → ℝ) :
    heterogeneousBenchmark x =
      5 + (5 / (n : ℝ)) * ∑ ij : Fin n × Fin 3, x ij.1 ij.2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrow (i : Fin n) :
      5 * (1 + x i 0 + x i 1 + x i 2) = 5 + 5 * ∑ j : Fin 3, x i j := by
    rw [Fin.sum_univ_three]
    ring
  unfold heterogeneousBenchmark
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hnR] <;> ring

/-- P029-T6: the heterogeneous benchmark has mean 5 and variance 25/n. -/
theorem heterogeneous_benchmark_moments_proof {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (X : Fin n → Fin 3 → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j))
    (hind : iIndepFun (fun ij : Fin n × Fin 3 => X ij.1 ij.2) μ)
    (hlaw : ∀ i j, Measure.map (X i j) μ = uniformMinusOneOne) :
    (∫ ω, heterogeneousBenchmark (fun i j => X i j ω) ∂μ) = 5 ∧
    mCov μ (fun ω => heterogeneousBenchmark (fun i j => X i j ω))
      (fun ω => heterogeneousBenchmark (fun i j => X i j ω)) = 25 / n := by
  let S : Ω → ℝ := fun ω => ∑ ij : Fin n × Fin 3, X ij.1 ij.2 ω
  obtain ⟨hS2, hSmean, hSvar⟩ := hbm_flattened_uniform_sum_moments μ n X hm hind hlaw
  change MemLp S 2 μ at hS2
  change (∫ ω, S ω ∂μ) = 0 at hSmean
  change variance S μ = (n : ℝ) at hSvar
  let B : Ω → ℝ := fun ω => heterogeneousBenchmark (fun i j => X i j ω)
  let A : Ω → ℝ := fun ω => 5 + (5 / (n : ℝ)) * S ω
  have hBA : B = A := by
    funext ω
    exact hbm_benchmark_affine_normalization n hn (fun i j => X i j ω)
  have hscaled2 : MemLp (fun ω => (5 / (n : ℝ)) * S ω) 2 μ :=
    hS2.const_mul (5 / (n : ℝ))
  have hA2 : MemLp A 2 μ := (memLp_const (5 : ℝ)).add hscaled2
  have hAmean : (∫ ω, A ω ∂μ) = 5 := by
    change (∫ ω, 5 + (5 / (n : ℝ)) * S ω ∂μ) = 5
    rw [integral_add (integrable_const (5 : ℝ))
      (hscaled2.integrable (by norm_num)), integral_const_mul, hSmean]
    simp
  have hAvar : variance A μ = 25 / (n : ℝ) := by
    change variance (fun ω => 5 + (5 / (n : ℝ)) * S ω) μ = 25 / (n : ℝ)
    rw [variance_const_add hscaled2.aestronglyMeasurable 5,
      variance_const_mul, hSvar]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hnR] <;> ring
  have hAcov : mCov μ A A = 25 / (n : ℝ) := by
    calc
      mCov μ A A = variance A μ := by
        rw [variance_eq_sub hA2]
        simp only [mCov, Pi.pow_apply, pow_two]
      _ = 25 / (n : ℝ) := hAvar
  change (∫ ω, B ω ∂μ) = 5 ∧ mCov μ B B = 25 / (n : ℝ)
  rw [hBA]
  exact ⟨hAmean, hAcov⟩

end

end AronowAudit.P029.Wave1
