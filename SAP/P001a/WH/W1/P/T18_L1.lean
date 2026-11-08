import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Gap.GLP0012B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L1

open AronowAudit.P001

private lemma wholeDesign_dotForm {K L : ℕ} (x : Fin K → ℝ) (w : Fin L → ℝ)
    (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ) :
    wholeDesign x w ⬝ᵥ Fin.cases a (Fin.addCases b c) =
      a + (∑ k, b k * x k) + ∑ k, c k * w k := by
  change (Fin.cases 1 (Fin.addCases x w)) ⬝ᵥ Fin.cases a (Fin.addCases b c) = _
  rw [dotProduct_comm]
  exact AronowAudit.P001.Wave1.CondP001b_aug_sum a b c x w

private lemma wholeRisk_form {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ)
    (D : Ω → ℝ) (a : ℝ) (b : Fin K → ℝ) (c : Fin L → ℝ) :
    wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D
        (Fin.cases a (Fin.addCases b c)) =
      mean μ (fun ω => (D ω -
        (a + (∑ k, b k * X ω k) + ∑ k, c k * W ω k)) ^ 2) := by
  unfold wholeRisk mean
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [wholeDesign_dotForm]

private lemma wholeRisk_ae_congr {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ)
    (D₁ D₂ : Ω → ℝ) (hD : D₁ =ᵐ[μ] D₂) (b : Fin (K + L + 1) → ℝ) :
    wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D₁ b =
      wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D₂ b := by
  unfold wholeRisk
  apply integral_congr_ae
  filter_upwards [hD] with ω hω
  rw [hω]

theorem _root_.SAP.P001a.WH.W1.T18_L1_proof : SAP.P001a.WH.W1.T18_L1 := by
  intro Ω _ μ _ K L X W D γ h
  let Dbin : Ω → ℝ := fun ω => if D ω = 1 then 1 else 0
  have hDmeas : Measurable Dbin := by
    dsimp [Dbin]
    exact Measurable.ite (measurableSet_eq_fun h.measurableD measurable_const)
      measurable_const measurable_const
  have hDae : Dbin =ᵐ[μ] D := by
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω
    · simp [Dbin, hω]
    · simp [Dbin, hω]
  have hDbinary : ∀ ω, Dbin ω = 0 ∨ Dbin ω = 1 := by
    intro ω
    by_cases hω : D ω = 1
    · right
      simp [Dbin, hω]
    · left
      simp [Dbin, hω]
  have hDset : {ω | Dbin ω = 1} = {ω | D ω = 1} := by
    ext ω
    by_cases hω : D ω = 1 <;> simp [Dbin, hω]
  have hCIbin : CI μ X h.measurableX W Dbin := by
    intro A B hA hB
    have hJoint : (fun ω => if W ω ∈ A ∧ Dbin ω ∈ B then (1 : ℝ) else 0) =ᵐ[μ]
        (fun ω => if W ω ∈ A ∧ D ω ∈ B then (1 : ℝ) else 0) := by
      filter_upwards [hDae] with ω hω
      simp [hω]
    have hDind : (fun ω => if Dbin ω ∈ B then (1 : ℝ) else 0) =ᵐ[μ]
        (fun ω => if D ω ∈ B then (1 : ℝ) else 0) := by
      filter_upwards [hDae] with ω hω
      simp [hω]
    filter_upwards [condExp_congr_ae hJoint, h.ci A B hA hB,
      condExp_congr_ae hDind] with ω hleft hci hright
    rw [hleft, hci, hright]
  have hCEFbin : IsCEF μ X Dbin (linearPredictor γ) := by
    refine ⟨h.cef.1, h.cef.2.1.congr hDae.symm, h.cef.2.2.1, ?_⟩
    intro A hA
    calc
      (∫ ω in X ⁻¹' A, Dbin ω ∂μ) = ∫ ω in X ⁻¹' A, D ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hDae)
      _ = ∫ ω in X ⁻¹' A, linearPredictor γ (X ω) ∂μ := h.cef.2.2.2 A hA
  have hRank : IsUnit (Matrix.det (fun j k : Fin (K + L + 1) =>
      mean μ (fun ω =>
        (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j) *
        (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k)))) := by
    change IsUnit (Matrix.det (wholeQ μ (fun ω => wholeDesign (X ω) (W ω))))
    exact h.rank
  have hSupportAudit : 0 < AronowAudit.P001.prob μ {ω | Dbin ω = 1} ∧
      AronowAudit.P001.prob μ {ω | Dbin ω = 1} < 1 := by
    simpa [AronowAudit.P001.prob, SAP.P001a.prob, hDset] using h.supportD
  have hPopBin := AronowAudit.P001.Wave1.placebo_linear_cef_correction_proof
      μ X W Dbin h.measurableX h.measurableW hDmeas hDbinary
      hSupportAudit h.secondX h.secondW hCIbin γ hCEFbin hRank
  have hCEForiginal : IsCEF μ (fun ω => (X ω, W ω)) D
      (fun xw => linearPredictor γ xw.1) := by
    refine ⟨hPopBin.1.1, h.cef.2.1, hPopBin.1.2.2.1, ?_⟩
    intro A hA
    calc
      (∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A, D ω ∂μ) =
          ∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A, Dbin ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hDae.symm)
      _ = ∫ ω in (fun ω => (X ω, W ω)) ⁻¹' A,
          linearPredictor γ ((X ω, W ω).1) ∂μ := hPopBin.1.2.2.2 A hA
  refine ⟨hCEForiginal, ?_⟩
  intro v
  let a : ℝ := v 0
  let b : Fin K → ℝ := fun k => v (Fin.castAdd L k).succ
  let c : Fin L → ℝ := fun k => v (Fin.natAdd K k).succ
  have hvform : Fin.cases a (Fin.addCases b c) = v := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [a]
    · refine Fin.addCases ?_ ?_ i
      · intro k
        simp [b, Fin.cases_succ, Fin.addCases_left]
      · intro k
        simp [c, Fin.cases_succ, Fin.addCases_right]
  have hbasebin : wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin
      (wholeNullCoef γ) = mean μ (fun ω => (Dbin ω - linearPredictor γ (X ω)) ^ 2) := by
    unfold wholeRisk mean
    apply integral_congr_ae
    filter_upwards [] with ω
    have hd : wholeDesign (X ω) (W ω) ⬝ᵥ wholeNullCoef γ = linearPredictor γ (X ω) := by
      change wholeDesign (X ω) (W ω) ⬝ᵥ
        Fin.cases (γ 0) (Fin.addCases (fun k => γ k.succ) (fun _ : Fin L => 0)) = _
      simpa [linearPredictor, Finset.sum_const_zero] using
        wholeDesign_dotForm (X ω) (W ω) (γ 0) (fun k => γ k.succ) (fun _ => 0)
    rw [hd]
  have hbase : wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D
      (wholeNullCoef γ) = mean μ (fun ω => (Dbin ω - linearPredictor γ (X ω)) ^ 2) := by
    calc
      wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ) =
          wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) :=
        wholeRisk_ae_congr μ X W D Dbin hDae.symm (wholeNullCoef γ)
      _ = _ := hbasebin
  have htargetbin : wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v =
      mean μ (fun ω => (Dbin ω -
        (a + (∑ k, b k * X ω k) + ∑ k, c k * W ω k)) ^ 2) := by
    rw [← hvform]
    exact wholeRisk_form μ X W Dbin a b c
  have htarget : wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D v =
      mean μ (fun ω => (Dbin ω -
        (a + (∑ k, b k * X ω k) + ∑ k, c k * W ω k)) ^ 2) := by
    calc
      wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D v =
          wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v :=
        wholeRisk_ae_congr μ X W D Dbin hDae.symm v
      _ = _ := htargetbin
  have hcoords : (a = γ 0 ∧ (∀ k, b k = γ k.succ) ∧ (∀ k, c k = 0)) ↔
      v = wholeNullCoef γ := by
    constructor
    · rintro ⟨ha, hb, hc⟩
      rw [← hvform]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [wholeNullCoef, a, ha]
      · refine Fin.addCases ?_ ?_ i
        · intro k
          simp [b, wholeNullCoef, hb]
        · intro k
          simp [c, wholeNullCoef, hc]
    · intro hv
      have ha : a = γ 0 := by
        have he := congrFun hv 0
        simpa [a, wholeNullCoef] using he
      have hb : ∀ k, b k = γ k.succ := by
        intro k
        have he := congrFun hv (Fin.castAdd L k).succ
        simpa [b, wholeNullCoef, Fin.cases_succ, Fin.addCases_left] using he
      have hc : ∀ k, c k = 0 := by
        intro k
        have he := congrFun hv (Fin.natAdd K k).succ
        simpa [c, wholeNullCoef, Fin.cases_succ, Fin.addCases_right] using he
      exact ⟨ha, hb, hc⟩
  constructor
  · have hmin := hPopBin.2.1 a b c
    rw [hbase, htarget]
    exact hmin
  · constructor
    · intro heq
      have heqbin : wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v =
          wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) := by
        calc
          wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v =
              wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D v :=
            wholeRisk_ae_congr μ X W Dbin D hDae v
          _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ) := heq
          _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) :=
            (wholeRisk_ae_congr μ X W Dbin D hDae (wholeNullCoef γ)).symm
      have hformeq := (hPopBin.2.2 a b c).1 (by
        calc
          mean μ (fun ω => (Dbin ω -
              (a + (∑ k, b k * X ω k) + ∑ k, c k * W ω k)) ^ 2) =
              wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v := htargetbin.symm
          _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) := heqbin
          _ = mean μ (fun ω => (Dbin ω - linearPredictor γ (X ω)) ^ 2) := hbasebin)
      exact hcoords.mp hformeq
    · intro hv
      have hformeq := hcoords.mpr hv
      have heqbin := (hPopBin.2.2 a b c).2 hformeq
      calc
        wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D v =
            wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v :=
          wholeRisk_ae_congr μ X W D Dbin hDae.symm v
        _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) := by
          calc
            wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin v =
                mean μ (fun ω => (Dbin ω -
                  (a + (∑ k, b k * X ω k) + ∑ k, c k * W ω k)) ^ 2) := htargetbin
            _ = mean μ (fun ω => (Dbin ω - linearPredictor γ (X ω)) ^ 2) := heqbin
            _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) Dbin (wholeNullCoef γ) :=
              hbasebin.symm
        _ = wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ) :=
          wholeRisk_ae_congr μ X W Dbin D hDae (wholeNullCoef γ)

end T18_L1
