import SAP.P018a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise

theorem mean_overlap_rational_limit : Tendsto (fun n : ℕ =>
    32*((n : ℝ)-1)*(2*(n : ℝ)-1)*(4*(n : ℝ)^2-9*(n : ℝ)+3)/(7*(n : ℝ)-3)^4)
    atTop (𝓝 (256/2401 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hf : ContinuousAt (fun t : ℝ =>
      32*(1-t)*(2-t)*(4-9*t+3*t^2)/(7-3*t)^4) 0 := by
    fun_prop (disch := norm_num)
  have hl := hf.tendsto.comp ht
  have he : (fun n : ℕ =>
      32*((n : ℝ)-1)*(2*(n : ℝ)-1)*(4*(n : ℝ)^2-9*(n : ℝ)+3)/(7*(n : ℝ)-3)^4) =ᶠ[atTop]
      (fun n : ℕ => 32*(1-(n : ℝ)⁻¹)*(2-(n : ℝ)⁻¹)*
        (4-9*(n : ℝ)⁻¹+3*((n : ℝ)⁻¹)^2)/(7-3*(n : ℝ)⁻¹)^4) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  apply Filter.Tendsto.congr' he.symm
  convert hl using 1 <;> norm_num [Function.comp_def]

 theorem repetitions_unbounded : ∀ B : ℕ, ∃ N : ℕ, 2 ≤ N ∧ ∃ d : Dyad N,
    B < concentratedRepeated.T N d := by
  intro B
  let i : Fin (B+2) := ⟨0,by omega⟩
  let j : Fin (B+2) := ⟨B+1,by omega⟩
  have hij : i < j := by change (0 : ℕ) < B+1; omega
  let d : Dyad (B+2) := AronowAudit.P018.Wave1.printed_mkDyad i j hij.ne
  have he : firstUnit d = i ∧ secondUnit d = j :=
    AronowAudit.P018.Wave1.printed_mkDyad_endpoints i j hij
  refine ⟨B+2,by omega,d,?_⟩
  change B < 2^((firstUnit d).val+(secondUnit d).val+2)
  rw [he.1,he.2]
  dsimp [i,j]
  have hb : B < 2^B := Nat.lt_two_pow_self
  exact hb.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

 theorem concentrated_limits (hTail : W1T9Tail) : W1T9Limits := by
  have : ∀ N : ℕ, IsProbabilityMeasure (unitSampleLaw signKernel N) := fun N => by
    unfold unitSampleLaw signKernel fairLaw
    infer_instance
  have hx : Tendsto W1x atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hW : Tendsto W1W atTop (𝓝 (1/3 : ℝ)) := by
    have hf : ContinuousAt (fun x : ℝ => (1-x)*(1-2*x)/3) 0 := by fun_prop
    have hh := hf.tendsto.comp hx
    have he (N : ℕ) : W1W N = (1-W1x N)*(1-2*W1x N)/3 :=
      AronowAudit.P018.Wave1.concentrated_weights_W_formula N
    convert hh using 1
    · funext N
      exact he N
    · norm_num
  have hD : Tendsto Dreal atTop atTop := by
    have hLower : ∀ N : ℕ, (N : ℝ)-1 ≤ Dreal N := by
      intro N
      by_cases hN : 2 ≤ N
      · have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
        dsimp [Dreal]
        nlinarith
      · interval_cases N <;> norm_num [Dreal]
    exact tendsto_atTop_mono hLower
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  refine ⟨?_,?_,hW.div_atTop hD,?_⟩
  · intro hc
    have hp := hc 1 (by norm_num)
    have hLower : ∀ᶠ N : ℕ in atTop, (1/256 : ℝ) ≤
        (unitSampleLaw signKernel N {ω | 1 ≤ |weightedOLS signKernel concentratedWeight ω 0|}).toReal := by
      filter_upwards [eventually_ge_atTop 8] with N hN
      have hWpos : (1/8 : ℝ) ≤ W1W N :=
        AronowAudit.P018.Wave1.concentrated_weights_W_lower (by omega)
      have hP : (unitSampleLaw signKernel N (W1WeightEvent N)).toReal = 1/256 :=
        AronowAudit.P018.Wave1.concentrated_weights_event_probability hN
      rw [← hP]
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      have hh := (hTail N hN).2.2 ω hω
      have hr := (hTail N hN).2.1
      have hb : 2-weightedOLS signKernel concentratedWeight ω 0 ≤ 1/8 := by
        have hR : 4*W1TailWeight N ≤ W1W N/8 := by linarith
        exact hh.2.1.trans ((div_le_iff₀ (by linarith : 0 < W1W N)).mpr (by linarith))
      exact (by dsimp; linarith [le_abs_self (weightedOLS signKernel concentratedWeight ω 0)])
    have hz : (1/256 : ℝ) ≤ 0 := ge_of_tendsto hp (by simpa only [Real.norm_eq_abs] using hLower)
    norm_num at hz
  · exact tendsto_natCast_atTop_atTop.atTop_mul_pos (by norm_num : (0 : ℝ) < 36/35)
      AronowAudit.P018.Wave1.concentrated_weights_variance_limit
  · have hf : ContinuousAt (fun x : ℝ => 3/(4*(1-x))) 0 := by fun_prop (disch := norm_num)
    simpa [Function.comp_def] using hf.tendsto.comp hx

/-- The converse deterministic probability limit, used for the point-mass obstruction. -/
theorem deterministic_limit_of_inProbability {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] {E : Type*} [NormedAddCommGroup E]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (A : ℕ → E) (h : AronowAudit.P018.inProbability μ (fun N _ => A N)) :
    Tendsto A atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp := h ε hε
  filter_upwards [hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with N hN
  rw [dist_zero_right]
  by_contra hn
  have he : {ω : Ω N | ε ≤ ‖A N‖} = Set.univ := by
    ext ω
    simp [le_of_not_gt hn]
  rw [he] at hN
  norm_num at hN

end SAP.P018a.WH.W1
