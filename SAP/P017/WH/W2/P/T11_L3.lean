import SAP.P017.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W2.P.T11_L3

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

theorem square_integrable_gaussian (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (2 : ℝ≥0)).integrable_norm_pow'
  simpa only [id_eq, Real.norm_eq_abs, sq_abs] using h

theorem gaussian_two_sided_tail (v : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ, if |x| > c then x ^ 2 else 0 ∂gaussianReal 0 v) =
      2 * (∫ x in Ioi c, x ^ 2 ∂gaussianReal 0 v) := by
  let γ := gaussianReal 0 v
  have hi : Integrable (fun x : ℝ => x ^ 2) γ := square_integrable_gaussian v
  have hip : Integrable (fun x : ℝ => if c < x then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Ioi : MeasurableSet (Ioi c)) using 1
    funext x
    rfl
  have hin : Integrable (fun x : ℝ => if x < -c then x ^ 2 else 0) γ := by
    convert hi.indicator (measurableSet_Iio : MeasurableSet (Iio (-c : ℝ))) using 1
    funext x
    rfl
  have hneg : (∫ x : ℝ, if x < -c then x ^ 2 else 0 ∂γ) =
      (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ) := by
    have hmap : γ.map (fun x : ℝ => -x) = γ := by
      simpa only [γ, neg_zero] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v))
    calc
      (∫ x : ℝ, if x < -c then x ^ 2 else 0 ∂γ) =
          (∫ x : ℝ, if c < -x then (-x) ^ 2 else 0 ∂γ) := by
            apply integral_congr_ae
            apply ae_of_all
            intro x
            have he : c < -x ↔ x < -c := by constructor <;> intro h <;> linarith
            simp only [he, neg_sq]
      _ = (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ.map (fun x : ℝ => -x)) := by
        rw [integral_map (by fun_prop)
          ((Measurable.ite measurableSet_Ioi (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
      _ = _ := by rw [hmap]
  have hsplit (x : ℝ) : (if |x| > c then x ^ 2 else 0) =
      (if x < -c then x ^ 2 else 0) + (if c < x then x ^ 2 else 0) := by
    by_cases hn : x < -c
    · have hp : ¬ c < x := by linarith
      have ha : c < |x| := by rw [abs_of_neg (by linarith)]; linarith
      simp only [hn, hp, ha, ↓reduceIte, add_zero]
    · by_cases hp : c < x
      · have ha : c < |x| := lt_of_lt_of_le hp (le_abs_self x)
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
      · have ha : ¬ c < |x| := not_lt.mpr (abs_le.mpr (by constructor <;> linarith))
        simp only [hn, hp, ha, ↓reduceIte, zero_add]
  simp_rw [hsplit]
  rw [integral_add hin hip, hneg]
  have hpos : (∫ x : ℝ, if c < x then x ^ 2 else 0 ∂γ) =
      ∫ x in Ioi c, x ^ 2 ∂γ := by
    simpa only [Set.indicator, mem_Ioi] using
      (integral_indicator (μ := γ) (f := fun x : ℝ => x ^ 2) measurableSet_Ioi)
  rw [hpos]
  ring

theorem gaussianPDFReal_scale (n : ℕ) (hn : 1 ≤ n) (σ x : ℝ)
    (hσ : 0 < σ) :
    gaussianPDFReal 0 (NNReal.mk ((σ / SAP.P017.sqrtN n) ^ 2)
        (sq_nonneg (σ / SAP.P017.sqrtN n))) x =
      (SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hroot : SAP.P017.sqrtN n ^ 2 = (n : ℝ) := by
    simp [SAP.P017.sqrtN, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hrootpos : 0 < SAP.P017.sqrtN n := by
    exact Real.sqrt_pos.mpr hnR
  have hs : 0 < σ / SAP.P017.sqrtN n := div_pos hσ hrootpos
  have hs2 : (σ / SAP.P017.sqrtN n) ^ 2 = σ ^ 2 / (n : ℝ) := by
    dsimp [SAP.P017.sqrtN]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hden : Real.sqrt (2 * Real.pi * (σ / SAP.P017.sqrtN n) ^ 2) =
      (σ / SAP.P017.sqrtN n) * Real.sqrt (2 * Real.pi) := by
    calc
      Real.sqrt (2 * Real.pi * (σ / SAP.P017.sqrtN n) ^ 2) =
          Real.sqrt (2 * Real.pi) * Real.sqrt ((σ / SAP.P017.sqrtN n) ^ 2) :=
        Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity) _
      _ = (σ / SAP.P017.sqrtN n) * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hs]
        ring
  unfold gaussianPDFReal
  simp only [NNReal.coe_mk, sub_zero]
  rw [hden]
  have hscale : ((σ / SAP.P017.sqrtN n) * Real.sqrt (2 * Real.pi))⁻¹ =
      SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi)) := by
    field_simp [ne_of_gt hs, ne_of_gt hrootpos, ne_of_gt hσ]
  rw [hscale]
  congr 2
  rw [hs2]
  field_simp [ne_of_gt hnR, ne_of_gt hσ]

end

end SAP.P017.WH.W2.P.T11_L3

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ENNReal NNReal Classical

theorem SAP.P017.WH.W2.T11_L3_proof : SAP.P017.WH.W2.T11_L3 := by
  intro n hn c σ hc hσ
  dsimp
  let s : ℝ := σ / SAP.P017.sqrtN n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsN : 0 < SAP.P017.sqrtN n := Real.sqrt_pos.mpr hnR
  have hs : 0 < s := by dsimp [s]; exact div_pos hσ hsN
  intro Ω mΩ P hP W hW hlaw
  let v : ℝ≥0 := NNReal.mk (s ^ 2) (sq_nonneg s)
  have hlawv : P.map W = gaussianReal 0 v := by
    rw [hlaw]
    congr 1
  have hsqG : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    exact SAP.P017.WH.W2.P.T11_L3.square_integrable_gaussian v
  have hsqMap : Integrable (fun x : ℝ => x ^ 2) (P.map W) := by
    rw [hlawv]
    exact hsqG
  have hsq : Integrable (fun ω => W ω ^ 2) P := by
    simpa only [Function.comp_def] using hsqMap.comp_measurable hW
  let g : ℝ → ℝ := fun x => if |x| > c then x ^ 2 else 0
  have hset : MeasurableSet {x : ℝ | |x| > c} := by
    exact measurableSet_lt measurable_const (by
      simpa only [Real.norm_eq_abs] using (measurable_id' : Measurable (fun x : ℝ => x)).norm)
  have hgG : Integrable g (gaussianReal 0 v) := by
    have hi := hsqG.indicator hset
    convert hi using 1
    funext x
    simp [g, Set.indicator]
  have hgMap : Integrable g (P.map W) := by
    rw [hlawv]
    exact hgG
  have hg : Integrable (fun ω => if |W ω| > c then W ω ^ 2 else 0) P := by
    have hcomp := hgMap.comp_measurable hW
    convert hcomp using 1
    funext ω
    rfl
  have hpull : (∫ ω, if |W ω| > c then W ω ^ 2 else 0 ∂P) =
      ∫ x : ℝ, if |x| > c then x ^ 2 else 0 ∂gaussianReal 0 v := by
    change _ = ∫ x : ℝ, g x ∂gaussianReal 0 v
    rw [← hlawv, integral_map hW.aemeasurable
      ((Measurable.ite hset (measurable_id'.pow_const 2) measurable_const).aestronglyMeasurable)]
  have htail := SAP.P017.WH.W2.P.T11_L3.gaussian_two_sided_tail v c hc
  have hvR : (v : ℝ) ≠ 0 := by
    dsimp [v]
    exact (sq_pos_of_pos hs).ne'
  have hv : v ≠ 0 := NNReal.coe_ne_zero.mp hvR
  have hrestrict : (∫ x in Ioi c, x ^ 2 ∂gaussianReal 0 v) =
      ∫ x in Ioi c, x ^ 2 * gaussianPDFReal 0 v x := by
    rw [← integral_indicator measurableSet_Ioi,
      integral_gaussianReal_eq_integral_smul hv]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Ioi c
    · simp only [Set.indicator_of_mem hx, smul_eq_mul, mul_comm]
    · simp only [Set.indicator_of_notMem hx, smul_zero]
  have hdensity : ∀ x : ℝ,
      gaussianPDFReal 0 v x =
        (SAP.P017.sqrtN n / (σ * Real.sqrt (2 * Real.pi))) *
          Real.exp (-(x ^ 2 * (n : ℝ)) / (2 * σ ^ 2)) := by
    intro x
    simpa only [v, s] using
      SAP.P017.WH.W2.P.T11_L3.gaussianPDFReal_scale n hn σ x hσ
  refine ⟨hsq, hg, ?_⟩
  rw [hpull, htail, hrestrict]
  unfold SAP.P017.normalTail
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change x ^ 2 * gaussianPDFReal 0 v x = _
  rw [hdensity x]
  ring
