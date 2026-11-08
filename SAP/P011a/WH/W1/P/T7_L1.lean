import SAP.P011a.WH.W1.Leaves
import AronowAudit.P011.Wave1.Gap.GP011B2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace SAP.P011a.WH.W1.P.T7_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

theorem capped_young_conservative (hq : WholeQuadraticLimit)
    (F : Family) (c1 c2 c3 c4 : ℝ) (h : WholeScaling F c1 c2 c3 c4)
    (hv : Valid F) :
    Conservative F (fun k y => VYoung
      (AronowAudit.P011.Wave1.GP011B2b_degree_only_comparisonCaps
        (Bridge.model (F.model k)).d ⌈c2⌉₊)
      (weighted (F.model k) y)) := by
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => AronowAudit.P011.Wave1.GP011B2b_degree_only_comparisonCaps
    (Bridge.model (F.model k)).d D
  let M := fun k => (1 : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ) +
    Matrix.diagonal (fun i => (c k i : ℝ))
  have hdeg (k : ℕ) (i : Fin (F.size k)) :
      AronowAudit.P011.degree (Bridge.model (F.model k)).G i ≤ D := by
    have hi : (AronowAudit.P011.degree (Bridge.model (F.model k)).G i : ℝ) ≤ c2 :=
      h.degrees k i
    have hc : c2 ≤ (D : ℝ) := Nat.le_ceil c2
    exact_mod_cast hi.trans hc
  have hc (k : ℕ) : ∀ i,
      AronowAudit.P011.degree (Bridge.model (F.model k)).G i ≤ c k i := by
    exact AronowAudit.P011.Wave1.GP011B2b_degree_only_comparisonCaps_valid
      _ _ _ D (hv k) (hdeg k)
  have hp (k : ℕ) : PSD (M k) ∧
      PSD (M k - oracleMatrix (F.model k).G) := by
    simpa [M, c, D, Bridge.model, SAP.P011a.PSD, AronowAudit.P011.PSD,
      SAP.P011a.quadratic, AronowAudit.P011.quadratic,
      SAP.P011a.oracleMatrix, AronowAudit.P011.oracleMatrix,
      SAP.P011a.adjacency, AronowAudit.P011.adjacency] using
      (AronowAudit.P011.Wave1.GP011B2b_degree_only_comparison_psd
        (Bridge.model (F.model k)).G (c k) (hc k))
  have hnorm (k : ℕ) : operatorNorm (M k) ≤ 1 + (D : ℝ) := by
    exact AronowAudit.P011.Wave1.GP011B2b_degree_only_comparison_norm
      (c k) D (fun _ => Nat.min_le_right _ _)
  have hcon := psd_conservative hq F c1 c2 c3 c4 (1 + (D : ℝ)) h M hp hnorm
  have hform (k : ℕ) (y : Fin (F.size k) → ℝ) :
      varianceForm (M k) (weighted (F.model k) y) =
        VYoung (c k) (weighted (F.model k) y) := by
    have hcn : ∀ i, c k i ≤ F.size k - 1 := by
      intro i
      exact (Nat.min_le_left _ _).trans (Nat.min_le_right _ _)
    simpa [M, c, Bridge.model, SAP.P011a.varianceForm,
      AronowAudit.P011.varianceForm, SAP.P011a.VYoung,
      AronowAudit.P011.VYoung, SAP.P011a.centered,
      AronowAudit.P011.centered, SAP.P011a.average,
      AronowAudit.P011.average, SAP.P011a.quadratic,
      AronowAudit.P011.quadratic, SAP.P011a.weighted,
      AronowAudit.P011.weighted, SAP.P011a.truncatedDegree,
      AronowAudit.P011.truncatedDegree] using
      (AronowAudit.P011.Wave1.GP011B2b_degree_only_comparison_form
        (c k) hcn (AronowAudit.P011.weighted (Bridge.model (F.model k)) y))
  simpa only [hform, c, D] using hcon

theorem centered_coordinate_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : WholeScaling F c1 c2 c3 c4) (k : ℕ) :
    ∀ᵐ y ∂(F.model k).law, ∀ i,
      |centered (weighted (F.model k) y) i| ≤ 2 * c1 := by
  have hb := h.bounded k
  have ha := AronowAudit.P011.HomoskedasticCompletion.beta_error_bound
    (F.positive k) (Bridge.model (F.model k)) c1 hb
  filter_upwards [hb, ha] with y hy hay
  change |betaHat (F.model k) y - beta (F.model k)| ≤ c1 at hay
  intro i
  have he : centered (weighted (F.model k) y) i =
      (weighted (F.model k) y i - beta (F.model k)) -
        (betaHat (F.model k) y - beta (F.model k)) := by
    unfold centered betaHat
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hy i])

end
end SAP.P011a.WH.W1.P.T7_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

theorem SAP.P011a.WH.W1.T7_L1_proof : SAP.P011a.WH.W1.T7_L1 := by
  intro hq F c1 c2 c3 c4 h hv hr A hm
  classical
  let D : ℕ := ⌈c2⌉₊
  let c := fun k => AronowAudit.P011.Wave1.GP011B2b_degree_only_comparisonCaps
    (SAP.P011a.Bridge.model (F.model k)).d D
  have hcon := SAP.P011a.WH.W1.P.T7_L1.capped_young_conservative
    hq F c1 c2 c3 c4 h hv
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  intro ε hε
  let η := Real.sqrt (ε / (8 * ((D : ℝ) + 1)))
  have hratio : 0 < ε / (8 * ((D : ℝ) + 1)) := by positivity
  have hη : 0 < η := Real.sqrt_pos.mpr hratio
  have hηsq : η ^ 2 = ε / (8 * ((D : ℝ) + 1)) := Real.sq_sqrt hratio.le
  have hsmall : (D : ℝ) * η ^ 2 ≤ ε / 8 := by
    rw [hηsq]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have he : ε / (8 * ((D : ℝ) + 1)) * (8 * ((D : ℝ) + 1)) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [hratio.le]
  obtain ⟨C, hC, hfinite⟩ :=
    AronowAudit.P011.Wave1.GP011B2b_uniform_comparison (2 * c1)
      (by linarith [h.c1_pos]) D η hη
  have hevent : ∀ᶠ k in atTop, C / (F.size k : ℝ) < ε / 4 :=
    (hN.const_div_atTop C).eventually
      (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (hcon (ε / 2) (by linarith))
  filter_upwards [hevent] with k hk
  letI : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  change (F.model k).law.real _ ≤ (F.model k).law.real _
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [SAP.P011a.WH.W1.P.T7_L1.centered_coordinate_bound
    F c1 c2 c3 c4 h k] with y hy
  let x := weighted (F.model k) y
  have hcx : ∀ i, |centered x i| ≤ 2 * c1 := by
    intro i
    exact hy i
  obtain ⟨G, hG, hcomp⟩ := hfinite (F.size k) (F.positive k) (c k)
    (fun _ => Nat.min_le_right _ _) (fun _ => (Nat.min_le_left _ _).trans
      (Nat.min_le_right _ _)) x hcx
  have hcompat : Compatible (F.model k).R (F.model k).d G := by
    constructor
    · intro i j hij
      rw [hr k] at hij
      exact hG.1 i j (by simpa [SAP.P011a.emptyGraph,
        AronowAudit.P011.emptyGraph] using hij)
    · intro i
      have hc : c k i ≤ (F.model k).d i := by
        exact (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
      exact (hG.2 i).trans hc
  have hmax : V1 G x ≤ V1 (A k y) x := (hm k y).2 G hcompat
  have hcmp : (F.size k : ℝ) *
      (VYoung (c k) x - V1 (A k y) x) ≤ C / (F.size k : ℝ) + D * η ^ 2 := by
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hmax _) (Nat.cast_nonneg _)).trans hcomp
  intro hbad
  change ε < (F.size k : ℝ) *
    (var (F.model k) (betaHat (F.model k)) - V1 (A k y) x) at hbad
  change ε / 2 < (F.size k : ℝ) *
    (var (F.model k) (betaHat (F.model k)) - VYoung (c k) x)
  nlinarith
