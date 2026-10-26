import AronowAudit.P004.Wave1.AreaSumBlueprint
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace AronowAudit.P004.Wave1.AreaSum

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

private def angleShare (z : ℂ) : ℝ :=
  (if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z) /
    (2 * Real.pi)

private theorem measurable_angleShare : Measurable angleShare := by
  exact (Measurable.ite (measurableSet_lt Complex.measurable_arg measurable_const)
    (Complex.measurable_arg.add_const (2 * Real.pi)) Complex.measurable_arg).div_const _

/-- On the polar chart, shares at most one half select a nonnegative angular interval. -/
private theorem angleShare_polar_iff (q : ℝ) (hq : q ≤ 1 / 2)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    angleShare (Complex.polarCoord.symm p) < q ↔
      0 ≤ p.2 ∧ p.2 < 2 * Real.pi * q := by
  have hr : 0 < p.1 := hp.1
  have hθ : -Real.pi < p.2 ∧ p.2 < Real.pi := hp.2
  have harg : Complex.arg (Complex.polarCoord.symm p) = p.2 := by
    rw [Complex.polarCoord_symm_apply, Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
  have htwo : 0 < 2 * Real.pi := by positivity
  have hqπ : q * (2 * Real.pi) ≤ Real.pi := by
    calc
      q * (2 * Real.pi) ≤ (1 / 2) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hq htwo.le
      _ = Real.pi := by ring
  dsimp [angleShare]
  rw [harg]
  by_cases hneg : p.2 < 0
  · rw [if_pos hneg, div_lt_iff₀ htwo]
    constructor
    · intro h
      exfalso
      linarith [hθ.1]
    · rintro ⟨h, -⟩
      exfalso
      linarith
  · rw [if_neg hneg, div_lt_iff₀ htwo]
    constructor
    · intro h
      exact ⟨le_of_not_gt hneg, by nlinarith⟩
    · rintro ⟨-, h⟩
      nlinarith

/-- The complex-plane calculation. The polar theorem already removes the null cut. -/
private theorem complex_annulus_sector (a b q : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    volume {z : ℂ | (a < ‖z‖ ∧ ‖z‖ ≤ b) ∧ angleShare z < q} =
      ENNReal.ofReal (q * Real.pi * (b ^ 2 - a ^ 2)) := by
  classical
  let S : Set ℂ := {z | (a < ‖z‖ ∧ ‖z‖ ≤ b) ∧ angleShare z < q}
  let R : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.Ico 0 (2 * Real.pi * q)
  have hS : MeasurableSet S := by
    exact ((measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)).inter
        (measurableSet_lt measurable_angleShare measurable_const)
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ico
  have hRsub : R ⊆ polarCoord.target := by
    intro p hp
    change (a < p.1 ∧ p.1 ≤ b) ∧ (0 ≤ p.2 ∧ p.2 < 2 * Real.pi * q) at hp
    change 0 < p.1 ∧ (-Real.pi < p.2 ∧ p.2 < Real.pi)
    have hqπ : 2 * Real.pi * q ≤ Real.pi := by
      calc
        2 * Real.pi * q ≤ 2 * Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ = Real.pi := by ring
    exact ⟨lt_of_le_of_lt ha hp.1.1, by linarith [Real.pi_pos, hp.2.1],
      lt_of_lt_of_le hp.2.2 hqπ⟩
  have hmem (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      Complex.polarCoord.symm p ∈ S ↔ p ∈ R := by
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    change (a < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ ≤ b) ∧
        angleShare (Complex.polarCoord.symm p) < q ↔
      (a < p.1 ∧ p.1 ≤ b) ∧ (0 ≤ p.2 ∧ p.2 < 2 * Real.pi * q)
    rw [hn, angleShare_polar_iff q hq p hp]
  have hpolar : volume S =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator (fun _ => (1 : ENNReal))
          (Complex.polarCoord.symm p) := by
    rw [Complex.lintegral_comp_polarCoord_symm, lintegral_indicator_const hS, one_mul]
  have hrect : volume S = ∫⁻ p in R, ENNReal.ofReal p.1 := by
    rw [hpolar]
    calc
      _ = ∫⁻ p in polarCoord.target,
          R.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p := by
        apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
        intro p hp
        by_cases hm : Complex.polarCoord.symm p ∈ S
        · have hm' : p ∈ R := (hmem p hp).mp hm
          simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hm',
            smul_eq_mul, mul_one]
        · have hm' : p ∉ R := fun h => hm ((hmem p hp).mpr h)
          simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm', smul_zero]
      _ = ∫⁻ p in R ∩ polarCoord.target, ENNReal.ofReal p.1 :=
        setLIntegral_indicator hR _
      _ = ∫⁻ p in R, ENNReal.ofReal p.1 := by rw [Set.inter_eq_left.mpr hRsub]
  have hradial : (∫⁻ r in Set.Ioc a b, ENNReal.ofReal r) =
      ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) := by
    have hi : IntegrableOn (fun r : ℝ => r) (Set.Ioc a b) :=
      (intervalIntegral.intervalIntegrable_id (μ := volume) (a := a) (b := b)).1
    have hn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] (fun r : ℝ => r) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact le_trans ha hr.1.le
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      ← intervalIntegral.integral_of_le hab, integral_id]
  have heval : (∫⁻ p in R, ENNReal.ofReal p.1) =
      ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) * ENNReal.ofReal (2 * Real.pi * q) := by
    change (∫⁻ p in Set.Ioc a b ×ˢ Set.Ico 0 (2 * Real.pi * q),
      ENNReal.ofReal p.1) = _
    rw [Measure.volume_eq_prod, setLIntegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal p.1)
      (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
    rw [lintegral_mul_const _ ENNReal.measurable_ofReal, hradial]
  change volume S = _
  have hdiff : 0 ≤ (b ^ 2 - a ^ 2) / 2 :=
    div_nonneg (sub_nonneg.mpr ((sq_le_sq₀ ha (ha.trans hab)).mpr hab)) (by norm_num)
  rw [hrect, heval, ← ENNReal.ofReal_mul hdiff]
  congr 1
  ring

/-- Euclidean area is transported through `ofLp` and the complex coordinate equivalence,
not by treating the sup-norm product as a Euclidean isometry. -/
theorem a4_proof : A4 := by
  classical
  intro c a b q ha hab hq0 hq
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℂ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans Complex.measurableEquivPi.symm
  have he : MeasurePreserving e volume volume :=
    Complex.volume_preserving_equiv_pi.symm.comp (PiLp.volume_preserving_ofLp (Fin 2))
  have he_apply (x : EuclideanSpace ℝ (Fin 2)) :
      e x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by rfl
  have he_norm (x : EuclideanSpace ℝ (Fin 2)) : ‖e x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [he_apply, Complex.sq_norm, Complex.normSq_add_mul_I,
      EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
  let S : Set ℂ := {z | (a < ‖z‖ ∧ ‖z‖ ≤ b) ∧ angleShare z < q}
  have hset :
      {x | a < dist x c ∧ dist x c ≤ b} ∩ {x | angularFraction c x < q} =
        (fun x : EuclideanSpace ℝ (Fin 2) => x + -c) ⁻¹' (e ⁻¹' S) := by
    ext x
    have hrad : ‖e (x + -c)‖ = dist x c := by
      rw [he_norm, dist_eq_norm, sub_eq_add_neg]
    have hang : angleShare (e (x + -c)) = angularFraction c x := by
      rw [he_apply]
      simp only [angleShare, angularFraction, PiLp.add_apply, PiLp.neg_apply,
        sub_eq_add_neg] <;> rfl
    change ((a < dist x c ∧ dist x c ≤ b) ∧ angularFraction c x < q) ↔
      ((a < ‖e (x + -c)‖ ∧ ‖e (x + -c)‖ ≤ b) ∧ angleShare (e (x + -c)) < q)
    rw [hrad, hang]
  rw [hset, measure_preimage_add_right volume (-c) (e ⁻¹' S),
    he.measure_preimage_equiv S]
  exact complex_annulus_sector a b q ha hab hq0 hq

end
end AronowAudit.P004.Wave1.AreaSum
