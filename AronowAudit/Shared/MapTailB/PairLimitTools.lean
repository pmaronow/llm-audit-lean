import AronowAudit.Shared.MapTailB.BoundedPairScore

/-! Probability and Gaussian linear-map adapters for finite product rows. -/
noncomputable section
namespace AronowAudit.Shared.MapTailB
open AronowAudit.P018 AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

theorem tb09_inProbability_prod {Ω : ℕ → Type*} [∀ N,MeasurableSpace (Ω N)]
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : ∀ N,Measure (Ω N)) [∀ N,IsProbabilityMeasure (P N)]
    (f : ∀ N,Ω N → E) (g : ∀ N,Ω N → F) (x : E) (y : F)
    (hf : inProbability P (fun N w => f N w-x))
    (hg : inProbability P (fun N w => g N w-y)) :
    inProbability P (fun N w => (f N w,g N w)-(x,y)) := by
  intro ε hε
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (by simpa only [add_zero] using (hf ε hε).add (hg ε hε))
  intro N
  convert WeightedConsistency.probability_union_bound P N
    {w | ε ≤ ‖f N w-x‖} {w | ε ≤ ‖g N w-y‖} using 1
  congr 2
  ext w
  simp only [Set.mem_setOf_eq,Set.mem_union,Prod.norm_def,Prod.fst_sub,
    Prod.snd_sub,le_max_iff]

theorem tb09_weak_mulVec {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ]
    (X : ∀ N,(Fin N → U) → Vec k) (A : ∀ N,(Fin N → U) → Mat k)
    (hXm : ∀ N,Measurable (X N)) (hAm : ∀ N,Measurable (A N))
    (G : Measure (Vec k)) (B : Mat k)
    (hX : weakLimit (fun N => Measure.pi (fun _ : Fin N => μ)) X G)
    (hA : inProbability (fun N => Measure.pi (fun _ : Fin N => μ))
      (fun N w => A N w-B)) :
    weakLimit (fun N => Measure.pi (fun _ : Fin N => μ))
      (fun N w => (A N w).mulVec (X N w)) (G.map (fun z => B.mulVec z)) := by
  letI tb09_mulVec_limit_probability : IsProbabilityMeasure G := hX.2.1
  let Q := GP0182B2b_product μ
  have hd : TendstoInDistribution (fun N w => X N (GP0182B2b_prefix N w))
      atTop id (fun _ => Q) G := by
    apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun N => ((hXm N).comp (GP0182B2b_prefix_measurable N)).aemeasurable)
      measurable_id.aemeasurable).mpr
    intro f
    have he (N : ℕ) : (∫ w,f (X N (GP0182B2b_prefix N w)) ∂Q)=
        ∫ w,f (X N w) ∂Measure.pi (fun _ : Fin N => μ) :=
      GP0182B2b_prefix_integral μ N _ (f.continuous.measurable.comp (hXm N))
    simpa only [Function.comp_def,he,id_eq] using hX.2.2 f
  let A' : ∀ N,(Fin N → U) → (Fin k → Fin k → ℝ) := fun N w => fun i j => A N w i j
  let B' : Fin k → Fin k → ℝ := fun i j => B i j
  have hAm' (N : ℕ) : Measurable (A' N) := hAm N
  have hA' : inProbability (fun N => Measure.pi (fun _ : Fin N => μ))
      (fun N w => A' N w-B') := hA
  have hAp := GP0182B2b_prefix_inProbability μ (fun N w => A' N w-B')
    (fun N => (hAm' N).sub measurable_const) hA'
  have hAp' : TendstoInMeasure Q (fun N w => A' N (GP0182B2b_prefix N w))
      atTop (fun _ => B') := by
    simpa only [tendstoInMeasure_iff_norm,sub_zero] using hAp
  have hj := hd.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : Vec k × (Fin k → Fin k → ℝ) => (Matrix.of z.2).mulVec z.1)
    (by fun_prop) hAp'
    (fun N => ((hAm' N).comp (GP0182B2b_prefix_measurable N)).aemeasurable)
  have hTm (N : ℕ) : Measurable (fun w => (A N w).mulVec (X N w)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec,dotProduct]
    exact Finset.measurable_fun_sum univ (fun j _ =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hAm N))).mul
        ((measurable_pi_apply j).comp (hXm N))))
  have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hj.forall_aemeasurable hj.aemeasurable_limit).1 hj
  refine ⟨fun N => (hTm N).aemeasurable,
    inferInstance,fun f => ?_⟩
  have he (N : ℕ) : (∫ w,f ((A N (GP0182B2b_prefix N w)).mulVec
      (X N (GP0182B2b_prefix N w))) ∂Q)=
      ∫ w,f ((A N w).mulVec (X N w)) ∂Measure.pi (fun _ : Fin N => μ) :=
    GP0182B2b_prefix_integral μ N _ (f.continuous.measurable.comp (hTm N))
  have hf := ht f
  change Tendsto (fun N => ∫ w,f ((A N (GP0182B2b_prefix N w)).mulVec
    (X N (GP0182B2b_prefix N w))) ∂Q) atTop (𝓝 (∫ z,f (B.mulVec z) ∂G)) at hf
  simpa only [he,integral_map (by fun_prop : AEMeasurable
    (fun z : Vec k => B.mulVec z) G) f.continuous.aestronglyMeasurable] using hf

theorem tb09_dot_mulVec {k : ℕ} (B : Mat k) (c z : Vec k) :
    dot c (B.mulVec z)=dot (B.transpose.mulVec c) z := by
  simp only [dot,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tb09_normal_linear {k : ℕ} (G : Measure (Vec k)) (V B : Mat k)
    (hG : centeredNormalLaw G V) :
    centeredNormalLaw (G.map (fun z => B.mulVec z)) (B*V*B.transpose) := by
  letI tb09_linear_probability : IsProbabilityMeasure G := hG.2.1
  refine ⟨?_,inferInstance,?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hG.1.mul_mul_conjTranspose_same B
  · intro c
    rw [Measure.map_map (by unfold dot; fun_prop) (by fun_prop)]
    have he : (fun z : Vec k => dot c (B.mulVec z))=
        fun z => dot (B.transpose.mulVec c) z := funext (tb09_dot_mulVec B c)
    change G.map (fun z => dot c (B.mulVec z)) = _
    rw [he,hG.2.2]
    congr 2
    simp only [← Matrix.mulVec_mulVec,tb09_dot_mulVec]

theorem tb09_inProbability_pi {Ω : ℕ → Type*} [∀ N,MeasurableSpace (Ω N)] {k : ℕ}
    (P : ∀ N,Measure (Ω N)) [∀ N,IsProbabilityMeasure (P N)]
    (f : ∀ N,Ω N → Vec k) (hf : ∀ j,inProbability P (fun N w => f N w j)) :
    inProbability P f := by
  intro ε hε
  have ht := WeightedConsistency.probability_finite_union_null P
    (fun N j => {w | ε ≤ |f N w j|}) (fun j => hf j ε hε)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ ht
  intro N
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw
  by_contra hn
  have hc : ∀ j,‖f N w j‖ < ε := by
    intro j
    apply lt_of_not_ge
    intro hj
    exact hn (Set.mem_iUnion.mpr ⟨j,hj⟩)
  exact (not_le.mpr ((pi_norm_lt_iff hε).mpr hc)) hw

theorem tb09_weak_eventually_eq {Ω : ℕ → Type*} [∀ N,MeasurableSpace (Ω N)]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (P : ∀ N,Measure (Ω N)) (X Y : ∀ N,Ω N → E) (G : Measure E)
    (hX : weakLimit P X G) (hY : ∀ N,AEMeasurable (Y N) (P N))
    (he : ∀ᶠ N in atTop,∀ w,X N w=Y N w) : weakLimit P Y G := by
  refine ⟨hY,hX.2.1,fun f => (hX.2.2 f).congr' ?_⟩
  filter_upwards [he] with N hN
  congr 1
  ext w
  rw [hN w]

theorem tb09_pair_meat_substitution {U E : Type*} [MeasurableSpace U]
    [NormedAddCommGroup E] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (q : ∀ N,(Fin N → U) → Dyad N → Vec k)
    (δ : ∀ N,(Fin N → U) → E) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ uv,‖h uv‖ ≤ B)
    (hd : ∀ N,2 ≤ N → ∀ w d,
      ‖h (w (firstUnit d),w (secondUnit d))-q N w d‖ ≤ L*‖δ N w‖)
    (hδ : inProbability (fun N => Measure.pi (fun _ : Fin N => μ)) δ) :
    inProbability (fun N => Measure.pi (fun _ : Fin N => μ)) (fun N w =>
      ((N:ℝ)/(Dreal N)^2) • meat members (q N w)-
      ((N:ℝ)/(Dreal N)^2) • meat members (fun d => h (w (firstUnit d),w (secondUnit d)))) := by
  let P := fun N => Measure.pi (fun _ : Fin N => μ)
  let φ : E → ℝ := fun z => 16*(2*B*(L*‖z‖)+(L*‖z‖)^2)
  have hφ0 : φ 0=0 := by simp [φ]
  have hz : inProbability P (fun N w => φ (δ N w)) := by
    have hh := WeightedConsistency.inProbability_continuousAt P
      (f := δ) (x := 0) (φ := φ) (by unfold φ; fun_prop)
      (by simpa only [sub_zero] using hδ)
    simpa only [hφ0,sub_zero] using hh
  apply WeightedConsistency.inProbability_ae_norm_le P _ _ hz
  filter_upwards [eventually_ge_atTop 2] with N hN
  apply ae_of_all
  intro w
  have hh := WeightedConsistency.meat_difference_norm_bound members
    (fun d => h (w (firstUnit d),w (secondUnit d))) (q N w)
    B (L*‖δ N w‖) hB (by positivity) (fun d => hb _) (hd N hN w)
  have hc : 0 ≤ 2*B*(L*‖δ N w‖)+(L*‖δ N w‖)^2 := by positivity
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (N:ℝ)/(Dreal N)^2 by positivity),
    abs_of_nonneg (show 0 ≤ φ (δ N w) by dsimp [φ]; positivity)]
  calc
    _ ≤ ((N:ℝ)/(Dreal N)^2)*((N:ℝ)^3*(2*B*(L*‖δ N w‖)+(L*‖δ N w‖)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hh.trans (mul_le_mul_of_nonneg_right (WeightedConsistency.g4_proof N).1 hc)
    _ = (((N:ℝ)/(Dreal N)^2)*(N:ℝ)^3)*(2*B*(L*‖δ N w‖)+(L*‖δ N w‖)^2) := by ring
    _ ≤ 16*(2*B*(L*‖δ N w‖)+(L*‖δ N w‖)^2) :=
      mul_le_mul_of_nonneg_right (WeightedConsistency.normalized_dyad_count_le hN) hc
    _ = _ := rfl

end AronowAudit.Shared.MapTailB
