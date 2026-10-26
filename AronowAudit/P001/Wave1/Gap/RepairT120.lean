import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.P001_PrintedRefutations
import Mathlib.MeasureTheory.Measure.Support

namespace AronowAudit.P001.Wave1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableRepairT120 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
universe u


private def RepairT120_binary (p y : ℝ) : ℝ :=
  if y = 1 then p else if y = 0 then 1-p else 0
private def RepairT120_κ : Measure ℝ := Measure.dirac 0 + Measure.dirac 1
private instance RepairT120_κ_finite : IsFiniteMeasure RepairT120_κ := by
  unfold RepairT120_κ; infer_instance
private theorem RepairT120_binary_meas (p : ℝ) : Measurable (RepairT120_binary p) := by
  unfold RepairT120_binary
  exact measurable_const.ite (measurableSet_singleton 1)
    (measurable_const.ite (measurableSet_singleton 0) measurable_const)
private theorem RepairT120_binary_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) :
    0 ≤ RepairT120_binary p y := by
  unfold RepairT120_binary
  split_ifs <;> linarith only [hp.1,hp.2]
private theorem RepairT120_binary_norm {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ y, ENNReal.ofReal (RepairT120_binary p y) ∂RepairT120_κ) = 1 := by
  simp only [RepairT120_κ, lintegral_add_measure, lintegral_dirac]
  norm_num [RepairT120_binary]
  rw [← ENNReal.ofReal_add (by linarith only [hp.2]) hp.1]
  norm_num

private def RepairT120_f (y : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  RepairT120_binary (if x 0 = 0 then 1/4 else 3/4) y
private def RepairT120_g (y : ℝ) (_ : Fin 1 → ℝ) (t : Fin 1 → ℝ) : ℝ :=
  RepairT120_binary (t 0) y
private def RepairT120_Θ : Set (Fin 1 → ℝ) :=
  {t | t 0 ∈ Set.Icc (1/10 : ℝ) (9/10)}
private theorem RepairT120_f_meas :
    Measurable (fun xy : (Fin 1 → ℝ) × ℝ => RepairT120_f xy.2 xy.1) := by
  have hm : Measurable (fun xy : (Fin 1 → ℝ) × ℝ =>
      if xy.1 0 = 0 then (1/4 : ℝ) else 3/4) :=
    measurable_const.ite
      ((measurable_pi_apply 0).comp measurable_fst (measurableSet_singleton 0)) measurable_const
  unfold RepairT120_f RepairT120_binary
  exact hm.ite (measurable_snd (measurableSet_singleton _))
    ((measurable_const.sub hm).ite (measurable_snd (measurableSet_singleton _)) measurable_const)
private theorem RepairT120_kl (t : Fin 1 → ℝ) :
    conditionalKL RepairT120_κ RepairT120_f RepairT120_g (fun _ => 0) t =
      bernoulliKL (1/4) (t 0) := by
  unfold conditionalKL RepairT120_κ
  rw [integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)]
  simp [RepairT120_f,RepairT120_g,RepairT120_binary,bernoulliKL]
  ring

/-- A finite alphabet makes every sample point binary, including null sample points. -/
private def RepairT120_law : Measure (Fin 4) :=
  (3/8 : ℝ≥0∞) • Measure.dirac 0 + (1/8 : ℝ≥0∞) • Measure.dirac 1 +
  (1/8 : ℝ≥0∞) • Measure.dirac 2 + (3/8 : ℝ≥0∞) • Measure.dirac 3
private instance RepairT120_law_probability : IsProbabilityMeasure RepairT120_law := by
  constructor
  norm_num [RepairT120_law,Measure.add_apply,Measure.smul_apply]
  rw [show (8 : ℝ≥0∞)⁻¹ = 1/8 from (one_div _).symm,
    ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]
  norm_num
  exact ENNReal.div_self (a := 8) (by norm_num) (by simp)
private def RepairT120_a : Fin 4 → ℝ := ![0,0,1,1]
private def RepairT120_b : Fin 4 → ℝ := ![0,1,0,1]
private def RepairT120_ν : Measure (Fin 1 → ℝ) :=
  (1/2 : ℝ≥0∞) • Measure.dirac (fun _ => 0) +
  (1/2 : ℝ≥0∞) • Measure.dirac (fun _ => 1)
private instance RepairT120_ν_probability : IsProbabilityMeasure RepairT120_ν := by
  constructor
  norm_num [RepairT120_ν,Measure.add_apply,Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two
private theorem RepairT120_cell_masses :
    RepairT120_ν {fun _ => 0} = 1/2 ∧ RepairT120_ν {fun _ => 1} = 1/2 := by
  have hne : (fun _ : Fin 1 => (0 : ℝ)) ≠ (fun _ => 1) := by
    intro h; have := congrFun h 0; norm_num at this
  simp [RepairT120_ν,Measure.add_apply,Measure.smul_apply,hne,hne.symm]

private theorem RepairT120_scalar_law :
    RepairT120_law.map (fun j => (RepairT120_a j,RepairT120_b j)) =
      (3/8 : ℝ≥0∞) • Measure.dirac (0,0) + (1/8 : ℝ≥0∞) • Measure.dirac (0,1) +
      (1/8 : ℝ≥0∞) • Measure.dirac (1,0) + (3/8 : ℝ≥0∞) • Measure.dirac (1,1) := by
  have hm := measurable_of_finite (fun j => (RepairT120_a j,RepairT120_b j))
  simp only [RepairT120_law,Measure.map_add _ _ hm,Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac]
  norm_num [RepairT120_a,RepairT120_b]
private theorem RepairT120_density :
    RepairT120_law.map (fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j)) =
      (RepairT120_ν.prod RepairT120_κ).withDensity
        (fun xy => ENNReal.ofReal (RepairT120_f xy.2 xy.1)) := by
  have hm := measurable_of_finite
    (fun j => ((fun _ : Fin 1 => RepairT120_a j),RepairT120_b j))
  simp only [RepairT120_law,Measure.map_add _ _ hm,Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac]
  norm_num [RepairT120_a,RepairT120_b,
    RepairT120_ν,RepairT120_κ,Measure.add_prod,Measure.prod_add,Measure.prod_smul_left,
    Measure.dirac_prod_dirac,withDensity_add_measure,withDensity_smul_measure,
    dirac_withDensity,RepairT120_f,RepairT120_binary,smul_smul]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
    div_eq_mul_inv, ← mul_assoc, ← ENNReal.mul_inv]
  have hc (r : ℝ≥0∞) : (2 : ℝ≥0∞)⁻¹ * r * (4 : ℝ≥0∞)⁻¹ =
      r * (8 : ℝ≥0∞)⁻¹ := by
    calc
      _ = r * ((2 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹) := by ac_rfl
      _ = _ := by rw [← ENNReal.mul_inv] <;> norm_num
  simp only [hc]
  ac_rfl

private theorem RepairT120_iid_comp {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] (μ : Measure Ω) (Z : ℕ → Ω → E)
    (hi : IID μ Z) (f : E → F) (hf : Measurable f) : IID μ (fun i ω => f (Z i ω)) :=
  ⟨fun i => hf.comp (hi.1 i),hi.2.1.comp (fun _ => f) (fun _ => hf),
    fun i => (hi.2.2 i).comp hf⟩

private theorem RepairT120_mle {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (hY : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (n : ℕ) (ω : Ω)
    (t : Fin 1 → ℝ) (ht : t ∈ RepairT120_Θ) (X : ℕ → Ω → Fin 1 → ℝ) :
    (∏ i ∈ Finset.range n,RepairT120_g (Y i ω) (X i ω) t) ≤
      ∏ i ∈ Finset.range n,RepairT120_g (Y i ω) (X i ω)
        (fun _ => clip (1/10) (9/10) (sampleMean Y n ω)) := by
  by_cases hn : n = 0
  · subst n; simp
  have hb (i : ℕ) (p : ℝ) : RepairT120_binary p (Y i ω) =
      if Y i ω = 1 then p else 1-p := by
    rcases hY i ω with h|h <;> simp [h,RepairT120_binary]
  simp only [RepairT120_g,hb]
  have hm := ((clipped_bernoulli_mle (Nat.pos_of_ne_zero hn)
    (fun i : Fin n => Y i.val ω) (fun i => hY i.val ω)).2 (t 0) ht).1
  rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n] at hm
  rw [Fin.prod_univ_eq_prod_range (fun i => if Y i ω = 1 then t 0 else 1-t 0) n,
    Fin.prod_univ_eq_prod_range (fun i => if Y i ω = 1 then
      clip (1/10) (9/10) ((∑ i ∈ Finset.range n, Y i ω) / (n : ℝ)) else
      1-clip (1/10) (9/10) ((∑ i ∈ Finset.range n, Y i ω) / (n : ℝ))) n] at hm
  exact hm


end
end AronowAudit.P001.Wave1
