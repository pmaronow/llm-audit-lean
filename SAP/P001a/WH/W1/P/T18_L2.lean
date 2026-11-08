import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Cond.CondP001bProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L2

lemma integralGram_posSemidef {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {p : ℕ} (V : Ω → Fin p → ℝ)
    (hV : ∀ j, MemLp (fun ω => V ω j) 2 μ) :
    Matrix.PosSemidef (fun j k => ∫ ω, V ω j * V ω k ∂μ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    change (∫ ω, V ω j * V ω i ∂μ) = ∫ ω, V ω i * V ω j ∂μ
    apply integral_congr_ae
    filter_upwards with ω
    ring
  · intro a
    have hpairs (i j : Fin p) : Integrable
        (fun ω => (a i * V ω i) * (a j * V ω j)) μ :=
      ((hV i).const_mul (a i)).integrable_mul ((hV j).const_mul (a j))
    have hinner (i : Fin p) : Integrable
        (fun ω => ∑ j, (a i * V ω i) * (a j * V ω j)) μ := by
      apply integrable_finsetSum
      intro j hj
      exact hpairs i j
    have hq :
        (∑ i, a i * ∑ j, ((∫ ω, V ω i * V ω j ∂μ) * a j)) =
          ∫ ω, (∑ i, a i * V ω i)^2 ∂μ := by
      calc
        (∑ i, a i * ∑ j, ((∫ ω, V ω i * V ω j ∂μ) * a j)) =
            ∑ i, ∑ j, ∫ ω, (a i * V ω i) * (a j * V ω j) ∂μ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          calc
            a i * ((∫ ω, V ω i * V ω j ∂μ) * a j) =
                (a i * a j) * ∫ ω, V ω i * V ω j ∂μ := by ring
            _ = ∫ ω, (a i * a j) * (V ω i * V ω j) ∂μ := by
              rw [integral_const_mul]
            _ = ∫ ω, (a i * V ω i) * (a j * V ω j) ∂μ := by
              congr 1
              funext ω
              ring
        _ = ∫ ω, (∑ i, a i * V ω i)^2 ∂μ := by
          symm
          calc
            (∫ ω, (∑ i, a i * V ω i)^2 ∂μ) =
                ∫ ω, ∑ i, ∑ j, (a i * V ω i) * (a j * V ω j) ∂μ := by
              congr 1
              funext ω
              rw [pow_two, Fintype.sum_mul_sum]
            _ = ∑ i, ∑ j, ∫ ω, (a i * V ω i) * (a j * V ω j) ∂μ := by
              rw [integral_finsetSum Finset.univ (fun i hi => hinner i)]
              apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finsetSum Finset.univ (fun j hj => hpairs i j)]
    rw [show star a ⬝ᵥ ((fun j k => ∫ ω, V ω j * V ω k ∂μ) *ᵥ a) =
      ∑ i, a i * ∑ j, ((∫ ω, V ω i * V ω j ∂μ) * a j) by
        simp [dotProduct, Matrix.mulVec, star_trivial]]
    rw [hq]
    exact integral_nonneg (fun ω => sq_nonneg _)

end SAP.P001a.WH.W1.P.T18_L2

theorem SAP.P001a.WH.W1.T18_L2_proof : SAP.P001a.WH.W1.T18_L2 := by
  intro Ω mΩ μ hμ K L X W D γ h hpop
  let C : Ω → (Fin K → ℝ) × (Fin L → ℝ) := fun ω => (X ω, W ω)
  let Z : Ω → Fin (K + L + 1) → ℝ := fun ω => wholeDesign (X ω) (W ω)
  let b : Fin (K + L + 1) → ℝ := wholeNullCoef γ
  let m : ((Fin K → ℝ) × (Fin L → ℝ)) → ℝ := fun xw => linearPredictor γ xw.1
  let R : Ω → ℝ := fun ω => wholeResidual Z D b ω
  have hC : Measurable C := h.measurableX.prodMk h.measurableW
  have hDesignMeas : Measurable
      (fun xw : (Fin K → ℝ) × (Fin L → ℝ) => wholeDesign xw.1 xw.2) := by
    apply measurable_pi_iff.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact measurable_const
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · have heq : (fun xw : (Fin K → ℝ) × (Fin L → ℝ) =>
            wholeDesign xw.1 xw.2 (Fin.castAdd L k).succ) = fun xw => xw.1 k := by
          funext xw
          simp [wholeDesign]
        rw [heq]
        exact (measurable_pi_apply k).comp measurable_fst
      · have heq : (fun xw : (Fin K → ℝ) × (Fin L → ℝ) =>
            wholeDesign xw.1 xw.2 (Fin.natAdd K k).succ) = fun xw => xw.2 k := by
          funext xw
          simp [wholeDesign]
        rw [heq]
        exact (measurable_pi_apply k).comp measurable_snd
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply j).comp hDesignMeas).comp hC
  have hZm (j : Fin (K + L + 1)) : MemLp (fun ω => Z ω j) 2 μ := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact memLp_const 1
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simpa [Z, wholeDesign] using h.secondX k
      · simpa [Z, wholeDesign] using h.secondW k
  have hD2 : MemLp D 2 μ := by
    apply MemLp.of_bound h.measurableD.aestronglyMeasurable 1
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hm2 : MemLp (fun ω => linearPredictor γ (X ω)) 2 μ :=
    AronowAudit.P001.Wave1.CondP001b_linear_memLp μ X h.secondX (γ 0)
      (fun k => γ k.succ)
  have hfit (ω : Ω) : Z ω ⬝ᵥ b = linearPredictor γ (X ω) := by
    change (∑ j, wholeDesign (X ω) (W ω) j * wholeNullCoef γ j) = _
    calc
      _ = ∑ j, wholeNullCoef γ j * wholeDesign (X ω) (W ω) j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = γ 0 + (∑ k, γ k.succ * X ω k) + ∑ k : Fin L, (0 : ℝ) * W ω k := by
        simpa [wholeNullCoef, wholeDesign] using
          AronowAudit.P001.Wave1.CondP001b_aug_sum (γ 0) (fun k => γ k.succ)
            (fun _ : Fin L => 0) (X ω) (W ω)
      _ = linearPredictor γ (X ω) := by simp [linearPredictor]
  have hR_eq : R = fun ω => D ω - linearPredictor γ (X ω) := by
    funext ω
    simp [R, wholeResidual, hfit]
  have hR2 : MemLp R 2 μ := by
    rw [hR_eq]
    exact hD2.sub hm2
  have hbinaryBounds : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hDnonneg : 0 ≤ᵐ[μ] D := hbinaryBounds.mono fun ω hω => hω.1
  have hDle : D ≤ᵐ[μ] fun _ => (1 : ℝ) := hbinaryBounds.mono fun ω hω => hω.2
  have hmce : (m ∘ C) =ᵐ[μ]
      μ[D | MeasurableSpace.comap C inferInstance] := by
    exact AronowAudit.P001.isCEF_condExp μ C hC D m hpop.1
  have hce0 : 0 ≤ᵐ[μ] μ[D | MeasurableSpace.comap C inferInstance] :=
    condExp_nonneg hDnonneg
  have hce1 : μ[D | MeasurableSpace.comap C inferInstance] ≤ᵐ[μ] fun _ => (1 : ℝ) :=
    condExp_le_nonneg_const (m := MeasurableSpace.comap C inferInstance)
      (c := 1) (by norm_num) hDle
  have hmBounds : ∀ᵐ ω ∂μ, linearPredictor γ (X ω) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hmce, hce0, hce1] with ω hce hlo hhi
    change m (C ω) ∈ Set.Icc (0 : ℝ) 1
    have hce' : m (C ω) = μ[D | MeasurableSpace.comap C inferInstance] ω := by
      simpa only [Function.comp_apply] using hce
    rw [hce']
    exact ⟨hlo, hhi⟩
  have hresBound : ∀ᵐ ω ∂μ, |R ω| ≤ 1 := by
    filter_upwards [h.binary, hmBounds] with ω hD hmω
    rw [hR_eq]
    rcases hD with hD | hD <;> simp [hD] at * <;> rcases hmω with ⟨hmlo, hmhi⟩ <;>
      simp only [abs_le] <;> constructor <;> linarith
  have horthCEF := AronowAudit.P001.cef_residual_orthogonality_correction
    μ C hC D hD2 m hpop.1 hm2
  have hmeanR : mean μ R = 0 := by
    rcases horthCEF with ⟨_, hmean, _⟩
    change (∫ ω, R ω ∂μ) = 0
    rw [hR_eq]
    simpa [AronowAudit.P001.mean, m, C] using hmean
  have horth (j : Fin (K + L + 1)) :
      mean μ (fun ω => Z ω j * R ω) = 0 := by
    rcases horthCEF with ⟨_, hmean, horth⟩
    have hgj : Measurable (fun xw : (Fin K → ℝ) × (Fin L → ℝ) =>
        wholeDesign xw.1 xw.2 j) := (measurable_pi_apply j).comp hDesignMeas
    have hgj2 : MemLp (fun ω => wholeDesign (X ω) (W ω) j) 2 μ := by
      simpa [Z] using hZm j
    have ho := horth (fun xw => wholeDesign xw.1 xw.2 j) hgj hgj2
    have ho' : covariance (fun ω => Z ω j) R μ = 0 := by
      simpa [Function.comp_def, C, Z, R, wholeResidual, m, hfit] using ho
    have hcov := covariance_eq_sub hgj2 hR2
    rw [hcov] at ho'
    have hmeanR' : (∫ ω, R ω ∂μ) = 0 := by simpa [mean] using hmeanR
    rw [hmeanR', mul_zero, sub_zero] at ho'
    change (∫ ω, Z ω j * R ω ∂μ) = 0
    exact ho'
  have hscore (j : Fin (K + L + 1)) :
      MemLp (fun ω => Z ω j * R ω) 2 μ := by
    apply (hZm j).abs.mono'
    · exact (((measurable_pi_apply j).comp hZ).aestronglyMeasurable.mul
      hR2.aestronglyMeasurable)
    · filter_upwards [hresBound] with ω hu
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |Z ω j| * |R ω| ≤ |Z ω j| * 1 := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        _ = |Z ω j| := by ring
  have hq : (wholeQ μ Z).PosSemidef := by
    change Matrix.PosSemidef (fun j k => ∫ ω, Z ω j * Z ω k ∂μ)
    exact SAP.P001a.WH.W1.P.T18_L2.integralGram_posSemidef (μ := μ) Z hZm
  let S : Ω → Fin (K + L + 1) → ℝ := fun ω => fun j => Z ω j * R ω
  have hOmegaEq : wholeOmega μ Z D b = fun j k => ∫ ω, S ω j * S ω k ∂μ := by
    ext j k
    apply integral_congr_ae
    filter_upwards with ω
    simp [S, R, wholeResidual]
    ring
  have hOmega : (wholeOmega μ Z D b).PosSemidef := by
    rw [hOmegaEq]
    exact SAP.P001a.WH.W1.P.T18_L2.integralGram_posSemidef (μ := μ) S hscore
  have hSandwich : (wholeSandwich μ Z D b).PosSemidef := by
    simpa [wholeSandwich] using hOmega.mul_mul_conjTranspose_same ((wholeQ μ Z)⁻¹)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hZ
  · exact h.measurableD
  · exact hZm
  · exact hresBound
  · exact horth
  · exact hscore
  · exact h.rank
  · exact hq
  · exact hOmega
  · exact hSandwich

