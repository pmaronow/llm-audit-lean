import AronowAudit.P018.Wave1.WeightedConsistency.M11
import AronowAudit.P018.Wave1.WeightedConsistency.G6

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem meat_difference_norm_bound {V E : Type*} [DecidableEq V] [Fintype E]
    (σ : E → Finset V) {k : ℕ} (q q' : E → Vec k) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hb : ∀ d, ‖q d‖ ≤ B) (hd : ∀ d, ‖q d - q' d‖ ≤ c) :
    ‖meat σ q' - meat σ q‖ ≤
      (∑ d, ((univ.filter (fun f => (σ d ∩ σ f).Nonempty)).card : ℝ)) * (2 * B * c + c^2) := by
  have hP : 0 ≤ 2 * B * c + c^2 := by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  have he (d f : E) :
      |(if (σ d ∩ σ f).Nonempty then q' d a * q' f b else 0) -
        (if (σ d ∩ σ f).Nonempty then q d a * q f b else 0)| ≤
        if (σ d ∩ σ f).Nonempty then 2 * B * c + c^2 else 0 := by
    split_ifs
    · have hh := residual_substitution_bound (q d a) (q f b)
          ((q d - q' d) a) ((q f - q' f) b) B c hB hc
          ((norm_le_pi_norm _ a).trans (hb d)) ((norm_le_pi_norm _ b).trans (hb f))
          ((norm_le_pi_norm _ a).trans (hd d)) ((norm_le_pi_norm _ b).trans (hd f))
      simpa only [Pi.sub_apply, sub_sub_cancel] using hh
    · simp
  change |(meat σ q' - meat σ q) a b| ≤ _
  simp only [meat, Matrix.sub_apply, Matrix.sum_apply, matrix_ite_apply, outer, Matrix.zero_apply, Pi.zero_apply]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d, |∑ f, ((if (σ d ∩ σ f).Nonempty then q' d a * q' f b else 0) -
        (if (σ d ∩ σ f).Nonempty then q d a * q f b else 0))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, ∑ f, if (σ d ∩ σ f).Nonempty then 2 * B * c + c^2 else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun f _ => he d f))
    _ = _ := by
      simp only [← Finset.sum_filter, sum_const, nsmul_eq_mul]
      rw [Finset.sum_mul]

/-- A.e. domination preserves convergence defined with outer probabilities. -/
theorem inProbability_ae_norm_le {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ∀ N, Ω N → E) (g : ∀ N, Ω N → F) (hg : inProbability μ g)
    (hb : ∀ᶠ N in atTop, ∀ᵐ ω ∂μ N, ‖f N ω‖ ≤ ‖g N ω‖) : inProbability μ f := by
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) _ (hg ε hε)
  filter_upwards [hb] with N hN
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hN] with ω hω
  exact fun h => h.trans hω

theorem m10_proof : M10.{u} := by
  intro g4 _ U _ k R X Y dir v C H hS hreg hcoef
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  letI instSamplesProbability : ∀ N, IsProbabilityMeasure (repeatedLaw R N) :=
    fun N => repeatedLaw_probability R hS.1 N
  let β := popBeta R.μ X Y
  let δ := fun N (ω : Fin N → U) => recordWeightedOLS R (v N) ω - β
  change inProbability (repeatedLaw R) δ at hcoef
  obtain ⟨B, hB, hb⟩ := hreg.2
  obtain ⟨Bq, hBq, hq⟩ := blockScore_uniform_bound R X Y dir v C H hS hreg β
  let L := 2 * (|C| * (k : ℝ) * B^2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let φ : Vec k → ℝ := fun z => 16 * (2 * Bq * (L * ‖z‖) + (L * ‖z‖)^2)
  have hφ : ContinuousAt φ 0 := by unfold φ; fun_prop
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hnull : inProbability (repeatedLaw R) (fun N ω => φ (δ N ω)) := by
    have hh := inProbability_continuousAt (repeatedLaw R) (f := δ) hφ
      (by simpa only [sub_zero] using hcoef)
    simpa only [hφ0, sub_zero] using hh
  apply inProbability_ae_norm_le (repeatedLaw R) _ _ hnull
  filter_upwards [eventually_ge_atTop 2] with N hN
  filter_upwards [ae_all_iff.mpr (fun d => ae_all_iff.mpr (fun t => hb N d t)),
    ae_all_iff.mpr (fun d => hq N d)] with ω hdata hqω
  have hchange (d : Dyad N) :
      ‖recordWeightedBlockScore R (v N) β ω d -
        recordWeightedBlockScore R (v N) (recordWeightedOLS R (v N) ω) ω d‖ ≤ L * ‖δ N ω‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have hid : (recordWeightedBlockScore R (v N) β ω d -
        recordWeightedBlockScore R (v N) (recordWeightedOLS R (v N) ω) ω d) a =
          ∑ t, v N d t * dot (repeatedX R ω d t) (δ N ω) * repeatedX R ω d t a := by
      simp only [recordWeightedBlockScore, score, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Finset.sum_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hdot : dot (repeatedX R ω d t) (δ N ω) =
          dot (repeatedX R ω d t) (recordWeightedOLS R (v N) ω) -
            dot (repeatedX R ω d t) β := by
        simp only [δ, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [hdot]
      ring
    simp only [Real.norm_eq_abs]
    rw [hid]
    calc
      _ ≤ ∑ t, |v N d t * dot (repeatedX R ω d t) (δ N ω) * repeatedX R ω d t a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin (R.T N d), |C| * ((k : ℝ) * B * ‖δ N ω‖) * B := by
        apply Finset.sum_le_sum
        intro t ht
        have hw : |v N d t| ≤ |C| := by
          rw [abs_of_pos (hS.2.2.2.1 N d t).1]
          exact (hS.2.2.2.1 N d t).2.trans (le_abs_self C)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul hw
          (abs_dot_le_of_norm_le _ _ B (hdata d t).1) (abs_nonneg _) (abs_nonneg _))
          ((norm_le_pi_norm _ a).trans (hdata d t).1) (abs_nonneg _) (by positivity)
      _ ≤ 2 * (|C| * ((k : ℝ) * B * ‖δ N ω‖) * B) := by
        simp only [sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast records_le_two R dir hS.2.1 N d) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hmeat := meat_difference_norm_bound members
    (recordWeightedBlockScore R (v N) β ω)
    (recordWeightedBlockScore R (v N) (recordWeightedOLS R (v N) ω) ω)
    Bq (L * ‖δ N ω‖) hBq (by positivity) hqω hchange
  have hP : 0 ≤ 2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2 := by positivity
  change ‖scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω -
    scaledMeatAt R v N β ω‖ ≤ |φ (δ N ω)|
  rw [abs_of_nonneg (show 0 ≤ φ (δ N ω) by dsimp [φ]; positivity)]
  unfold scaledMeatAt
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (N : ℝ) / (Dreal N)^2 by positivity)]
  calc
    _ ≤ ((N : ℝ) / (Dreal N)^2) *
        ((N : ℝ)^3 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmeat.trans (mul_le_mul_of_nonneg_right (g4 N).1 hP)
    _ = (((N : ℝ) / (Dreal N)^2) * (N : ℝ)^3) *
        (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) := by ring
    _ ≤ 16 * (2 * Bq * (L * ‖δ N ω‖) + (L * ‖δ N ω‖)^2) :=
      mul_le_mul_of_nonneg_right (normalized_dyad_count_le hN) hP
    _ = _ := rfl

end
end AronowAudit.P018.Wave1.WeightedConsistency
