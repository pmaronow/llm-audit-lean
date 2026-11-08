import SAP.P001a.WH.W1.Leaves
import SAP.P001a.WH.W1.Support
import AronowAudit.P001.Wave1.Cond.CondP001bProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L3

private lemma whole_design_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K L : ℕ}
    (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ)
    (hX : ∀ k, MemLp (fun ω => X ω k) 2 μ)
    (hW : ∀ l, MemLp (fun ω => W ω l) 2 μ)
    (j : Fin (K + L + 1)) :
    MemLp (fun ω => wholeDesign (X ω) (W ω) j) 2 μ := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [wholeDesign] using
      (memLp_const (μ := μ) (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ)
  · refine Fin.addCases (fun k => ?_) (fun l => ?_) i
    · simpa [wholeDesign] using hX k
    · simpa [wholeDesign] using hW l

private lemma whole_design_linear_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K L : ℕ}
    (Z : Ω → Fin (K + L + 1) → ℝ) (hZm : Measurable Z)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) (a : Fin (K + L + 1) → ℝ) :
    MemLp (fun ω => Z ω ⬝ᵥ a) 2 μ := by
  have hm : MemLp (fun ω => ∑ j, a j * Z ω j) 2 μ :=
    memLp_finsetSum _ (fun j _ => (hZ j).const_mul (a j))
  have hmeas : Measurable (fun ω => Z ω ⬝ᵥ a) := by fun_prop
  exact hm.congr_norm hmeas.aestronglyMeasurable
    (ae_of_all μ (fun ω => by simp [dotProduct, mul_comm]))

private lemma whole_quadratic_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {p : ℕ} (Z : Ω → Fin p → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) (v : Fin p → ℝ) :
    (∫ ω, (Z ω ⬝ᵥ v) ^ 2 ∂μ) = v ⬝ᵥ (wholeQ μ Z).mulVec v := by
  have h := AronowAudit.P001.Wave1.DecideB_mean_linear_mul
    μ Z Z hZ hZ v v
  calc
    (∫ ω, (Z ω ⬝ᵥ v) ^ 2 ∂μ) =
        AronowAudit.P001.mean μ
          (fun ω => (∑ j, v j * Z ω j) * (∑ k, v k * Z ω k)) := by
      unfold AronowAudit.P001.mean
      congr 1
      funext ω
      have hform : Z ω ⬝ᵥ v = ∑ j, v j * Z ω j := by
        simp [dotProduct, mul_comm]
      rw [hform]
      ring
    _ = ∑ j, ∑ k, v j * AronowAudit.P001.mean μ
          (fun ω => Z ω j * Z ω k) * v k := h
    _ = v ⬝ᵥ (wholeQ μ Z).mulVec v := by
      simp [AronowAudit.P001.mean, wholeQ, Matrix.mulVec, dotProduct,
        Finset.mul_sum, mul_assoc]

end SAP.P001a.WH.W1.P.T18_L3

theorem SAP.P001a.WH.W1.T18_L3_proof : SAP.P001a.WH.W1.T18_L3 := by
  intro Ω mΩ μ hμ K L X W D h
  let Z : Ω → Fin (K + L + 1) → ℝ := fun ω => wholeDesign (X ω) (W ω)
  have hZm : Measurable Z := by
    apply measurable_pi_lambda
    intro j
    dsimp [Z, wholeDesign]
    refine Fin.cases ?_ (fun i => ?_) j
    · exact measurable_const
    · refine Fin.addCases (fun k => ?_) (fun l => ?_) i
      · simpa only [Fin.cases_succ, Fin.addCases_left] using
          (show Measurable (fun ω => X ω k) from by
            simpa [Function.comp_def] using
              (measurable_pi_apply k).comp h.measurableX)
      · simpa only [Fin.cases_succ, Fin.addCases_right] using
          (show Measurable (fun ω => W ω l) from by
            simpa [Function.comp_def] using
              (measurable_pi_apply l).comp h.measurableW)
  have hZ (j : Fin (K + L + 1)) : MemLp (fun ω => Z ω j) 2 μ := by
    exact SAP.P001a.WH.W1.P.T18_L3.whole_design_memLp μ X W h.secondX h.secondW j
  have hD : MemLp D 2 μ := by
    apply MemLp.of_bound h.measurableD.aestronglyMeasurable 1
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  let c : Fin (K + L + 1) → ℝ := fun j => ∫ ω, Z ω j * D ω ∂μ
  let b : Fin (K + L + 1) → ℝ := (wholeQ μ Z)⁻¹.mulVec c
  have hnormal : (wholeQ μ Z).mulVec b = c := by
    dsimp [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.rank]
    simp
  have hlin (a : Fin (K + L + 1) → ℝ) :
      MemLp (fun ω => Z ω ⬝ᵥ a) 2 μ :=
    SAP.P001a.WH.W1.P.T18_L3.whole_design_linear_memLp μ Z hZm hZ a
  have hres : MemLp (fun ω => D ω - Z ω ⬝ᵥ b) 2 μ := hD.sub (hlin b)
  have hnormalCoord (j : Fin (K + L + 1)) :
      ∫ ω, Z ω j * (D ω - Z ω ⬝ᵥ b) ∂μ = 0 := by
    have hprodD : Integrable (fun ω => Z ω j * D ω) μ := (hZ j).integrable_mul hD
    have hprodLin : Integrable (fun ω => Z ω j * (Z ω ⬝ᵥ b)) μ :=
      (hZ j).integrable_mul (hlin b)
    have hmul := AronowAudit.P001.Wave1.DecideB_mean_linear_mul
      μ Z Z hZ hZ (fun i => if i = j then 1 else 0) b
    have hprod : ∫ ω, Z ω j * (Z ω ⬝ᵥ b) ∂μ =
        ((wholeQ μ Z).mulVec b) j := by
      simpa [AronowAudit.P001.mean, wholeQ, Matrix.mulVec, dotProduct,
        Finset.mul_sum, mul_assoc, mul_comm] using hmul
    have hsplit :
        (∫ ω, Z ω j * (D ω - Z ω ⬝ᵥ b) ∂μ) =
          ∫ ω, Z ω j * D ω - Z ω j * (Z ω ⬝ᵥ b) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (fun ω => by ring)
    rw [hsplit, integral_sub hprodD hprodLin, hprod, hnormal]
    simp [c]
  have hcross (v : Fin (K + L + 1) → ℝ) :
      ∫ ω, (Z ω ⬝ᵥ v) * (D ω - Z ω ⬝ᵥ b) ∂μ = 0 := by
    let R : Ω → Fin 1 → ℝ := fun ω _ => D ω - Z ω ⬝ᵥ b
    have hR (i : Fin 1) : MemLp (fun ω => R ω i) 2 μ := by
      simpa [R] using hres
    have hmul := AronowAudit.P001.Wave1.DecideB_mean_linear_mul
      μ Z R hZ hR v (fun _ => 1)
    have hzero (j : Fin (K + L + 1)) :
        AronowAudit.P001.mean μ (fun ω => Z ω j * R ω 0) = 0 := by
      simpa [AronowAudit.P001.mean, R] using hnormalCoord j
    calc
      (∫ ω, (Z ω ⬝ᵥ v) * (D ω - Z ω ⬝ᵥ b) ∂μ) =
          AronowAudit.P001.mean μ
            (fun ω => (∑ j, v j * Z ω j) * (∑ i, (fun _ => 1) i * R ω i)) := by
        unfold AronowAudit.P001.mean
        congr 1
        funext ω
        simp [R, dotProduct, mul_comm]
      _ = ∑ j, ∑ i, v j *
            AronowAudit.P001.mean μ (fun ω => Z ω j * R ω i) * (fun _ => 1) i := hmul
      _ = 0 := by
        simp [hzero]
  have hquad (v : Fin (K + L + 1) → ℝ) :
      (∫ ω, (Z ω ⬝ᵥ v) ^ 2 ∂μ) = v ⬝ᵥ (wholeQ μ Z).mulVec v :=
    SAP.P001a.WH.W1.P.T18_L3.whole_quadratic_integral μ Z hZ v
  have hrisk (a : Fin (K + L + 1) → ℝ) :
      wholeRisk μ Z D a = wholeRisk μ Z D b +
        (a - b) ⬝ᵥ (wholeQ μ Z).mulVec (a - b) := by
    let v := a - b
    let R := fun ω => D ω - Z ω ⬝ᵥ b
    let T := fun ω => Z ω ⬝ᵥ v
    have hT : MemLp T 2 μ := by simpa [T, v] using hlin (a - b)
    have hRT : Integrable (fun ω => T ω * R ω) μ := hT.integrable_mul hres
    have hsum : Integrable (fun ω => R ω ^ 2 + T ω ^ 2) μ :=
      hres.integrable_sq.add hT.integrable_sq
    have hcrossInt : Integrable (fun ω => 2 * (T ω * R ω)) μ := hRT.const_mul 2
    have hpoint (ω : Ω) : (D ω - Z ω ⬝ᵥ a) ^ 2 =
        R ω ^ 2 + T ω ^ 2 - 2 * (T ω * R ω) := by
      dsimp [R, T, v]
      simp only [dotProduct_sub, Pi.sub_apply]
      ring
    calc
      wholeRisk μ Z D a = ∫ ω, R ω ^ 2 + T ω ^ 2 - 2 * (T ω * R ω) ∂μ := by
        unfold wholeRisk
        apply integral_congr_ae
        exact ae_of_all μ hpoint
      _ = (∫ ω, R ω ^ 2 ∂μ) + (∫ ω, T ω ^ 2 ∂μ) -
            2 * (∫ ω, T ω * R ω ∂μ) := by
        rw [integral_sub hsum hcrossInt, integral_add hres.integrable_sq hT.integrable_sq,
          integral_const_mul]
      _ = wholeRisk μ Z D b +
            (a - b) ⬝ᵥ (wholeQ μ Z).mulVec (a - b) := by
        rw [hcross (a - b), hquad (a - b)]
        simp [wholeRisk, R, T, v]
  have hrankMean : IsUnit (Matrix.det
      (fun j k => AronowAudit.P001.mean μ (fun ω => Z ω j * Z ω k))) := by
    have hRankQ : IsUnit (wholeQ μ Z).det := by
      simpa [Z] using h.rank
    change IsUnit (Matrix.det (fun j k => ∫ ω, Z ω j * Z ω k ∂μ))
    exact hRankQ
  change
    (∀ a, wholeRisk μ Z D a = wholeRisk μ Z D b +
      (a - b) ⬝ᵥ (wholeQ μ Z).mulVec (a - b)) ∧
    ((∃ γ : Fin (K + 1) → ℝ,
       wholeRisk μ Z D (wholeNullCoef γ) = wholeRisk μ Z D b) ↔
      (wholePlaceboSelector K L).mulVec b = 0)
  refine ⟨hrisk, ?_⟩
  constructor
  · rintro ⟨γ, heq⟩
    have hquad0 :
        (wholeNullCoef γ - b) ⬝ᵥ (wholeQ μ Z).mulVec (wholeNullCoef γ - b) = 0 := by
      have := hrisk (wholeNullCoef γ)
      linarith
    have hintegral0 :
        ∫ ω, (Z ω ⬝ᵥ (wholeNullCoef (K := K) (L := L) γ - b)) ^ 2 ∂μ = 0 := by
      rw [hquad (wholeNullCoef (K := K) (L := L) γ - b)]
      exact hquad0
    have hsq := (integral_eq_zero_iff_of_nonneg
      (fun ω => sq_nonneg (Z ω ⬝ᵥ (wholeNullCoef (K := K) (L := L) γ - b)))
      (hlin (wholeNullCoef (K := K) (L := L) γ - b)).integrable_sq).mp hintegral0
    have hzero :
        (fun ω => Z ω ⬝ᵥ (wholeNullCoef (K := K) (L := L) γ - b)) =ᵐ[μ] 0 := by
      filter_upwards [hsq] with ω hω
      exact sq_eq_zero_iff.mp hω
    have hzeroSum :
        (fun ω => ∑ j, (wholeNullCoef (K := K) (L := L) γ - b) j * Z ω j) =ᵐ[μ] 0 := by
      filter_upwards [hzero] with ω hω
      simpa [dotProduct, mul_comm] using hω
    have hcoef := AronowAudit.P001.Wave1.CondP001b_gram_unique
      μ Z hZ hrankMean (wholeNullCoef (K := K) (L := L) γ - b) hzeroSum
    have hvec : wholeNullCoef (K := K) (L := L) γ = b := by
      ext j
      have hj := congrFun hcoef j
      exact sub_eq_zero.mp hj
    have hnull := SAP.P001a.WH.W1.placebo_test_null (K := K) (L := L) γ
    rw [hvec] at hnull
    exact hnull
  · intro hsel
    have hblock (l : Fin L) : b ((Fin.natAdd K l).succ) = 0 := by
      have hl := congrFun hsel l
      simpa [wholePlaceboSelector, Matrix.mulVec, dotProduct] using hl
    let γ : Fin (K + 1) → ℝ := Fin.cases (b 0)
      (fun k => b ((Fin.castAdd L k).succ))
    have hvec : wholeNullCoef γ = b := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [wholeNullCoef, γ]
      · refine Fin.addCases (fun k => ?_) (fun l => ?_) i
        · simp [wholeNullCoef, γ]
        · simp [wholeNullCoef, γ, hblock l]
    refine ⟨γ, ?_⟩
    rw [hrisk, hvec]
    simp

