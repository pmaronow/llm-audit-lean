import AronowAudit.P018.Wave1.Gap.GP0182B2b
import AronowAudit.P001.Wave1.Gap.DecideB
import AronowAudit.Shared.MapTailB.RowLimits

/-! Bounded symmetric pair kernels on the actual finite iid product rows. -/

noncomputable section
namespace AronowAudit.Shared.MapTailB
open AronowAudit.P018 AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

theorem tb09_pair_measurable {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    {N : ℕ} (h : U × U → E) (hm : Measurable h) (d : Dyad N) :
    Measurable (fun w : Fin N → U => h (w (firstUnit d), w (secondUnit d))) :=
  hm.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

theorem tb09_pair_memLp {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → ℝ)
    (hm : Measurable h) {B : ℝ} (hb : ∀ uv, |h uv| ≤ B) (p : ℝ≥0∞) :
    MemLp h p (μ.prod μ) :=
  MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ hb)

/-- A bounded pair average converges without a symmetry assumption. -/
theorem tb09_pair_lln {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → ℝ)
    (hm : Measurable h) (hb : ∃ B : ℝ, ∀ uv, |h uv| ≤ B) :
    inProbability (fun N => Measure.pi (fun _ : Fin N => μ))
      (fun N w => GP0182B2b_dyadAverage h w - ∫ uv, h uv ∂μ.prod μ) := by
  obtain ⟨B,hB⟩ := hb
  let P := fun N => Measure.pi (fun _ : Fin N => μ)
  have hp (N : ℕ) : MemLp (GP0182B2b_dyadAverage h (N := N)) 2 (P N) := by
    apply MemLp.const_mul
    exact memLp_finsetSum _ (fun d _ =>
      MemLp.of_bound (tb09_pair_measurable h hm d).aestronglyMeasurable B
        (ae_of_all _ (fun w => hB _)))
  have hv := WeightedConsistency.dyad_scaled_variance_tendsto
    WeightedConsistency.g3_proof WeightedConsistency.g4_proof μ
    (fun N d w => h (w (firstUnit d),w (secondUnit d))) B
    (fun N d => tb09_pair_measurable h hm d)
    (fun N d w w' he => by rw [he _ (firstUnit_mem d), he _ (secondUnit_mem d)])
    (fun N d => ae_of_all _ (fun w => hB _))
  have hz := WeightedConsistency.centered_scalar_probability P _ hp hv
  apply WeightedConsistency.inProbability_eventually_eq P (hf := hz)
  filter_upwards [eventually_ge_atTop 2] with N hN w
  have he (d : Dyad N) : (∫ w : Fin N → U,
      h (w (firstUnit d),w (secondUnit d)) ∂P N) = ∫ uv,h uv ∂μ.prod μ :=
    GP0182B2b_kernel_pair_integral _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i) hm
      (firstUnit_ne_secondUnit d)
  have hi (d : Dyad N) : Integrable (fun w : Fin N → U =>
      h (w (firstUnit d),w (secondUnit d))) (P N) :=
    (MemLp.of_bound (tb09_pair_measurable h hm d).aestronglyMeasurable B
      (ae_of_all _ (fun w => hB _)) : MemLp _ 2 _).integrable one_le_two
  congr 1
  simp only [GP0182B2b_dyadAverage, integral_const_mul,
    integral_finsetSum _ (fun d _ => hi d), he, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, printed_card_real]
  rw [inv_mul_cancel_left₀ (printed_Dpos hN).ne']

/-- Fluctuations of the bounded overlap meat, with arbitrary vector pair scores. -/
theorem tb09_pair_meat_centered {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (hm : Measurable h) (hb : ∃ B : ℝ, ∀ uv, ‖h uv‖ ≤ B) :
    let P := fun N => Measure.pi (fun _ : Fin N => μ)
    let F := fun N (w : Fin N → U) => ((N:ℝ)/(Dreal N)^2) •
      meat members (fun d => h (w (firstUnit d),w (secondUnit d)))
    inProbability P (fun N w => F N w - meanMat (P N) (F N)) := by
  classical
  obtain ⟨B,hB⟩ := hb
  let B' := |B|
  have hB' : 0 ≤ B' := abs_nonneg B
  have hc (uv : U × U) (a : Fin k) : |h uv a| ≤ B' :=
    (norm_le_pi_norm (h uv) a).trans ((hB uv).trans (le_abs_self B))
  let P := fun N => Measure.pi (fun _ : Fin N => μ)
  let Z := fun (N : ℕ) (a b : Fin k) (p : Dyad N × Dyad N) (w : Fin N → U) =>
    if overlap p.1 p.2 then h (w (firstUnit p.1),w (secondUnit p.1)) a *
      h (w (firstUnit p.2),w (secondUnit p.2)) b else 0
  let F := fun N (w : Fin N → U) => ((N:ℝ)/(Dreal N)^2) •
      meat members (fun d => h (w (firstUnit d),w (secondUnit d)))
  have hmZ (N : ℕ) (a b : Fin k) (p : Dyad N × Dyad N) : Measurable (Z N a b p) := by
    dsimp [Z]
    split_ifs
    · exact ((measurable_pi_apply a).comp (tb09_pair_measurable h hm p.1)).mul
        ((measurable_pi_apply b).comp (tb09_pair_measurable h hm p.2))
    · exact measurable_const
  have hs (N : ℕ) (a b : Fin k) (p : Dyad N × Dyad N) (w w' : Fin N → U)
      (he : ∀ i ∈ WeightedConsistency.pairSupport p, w i = w' i) :
      Z N a b p w = Z N a b p w' := by
    dsimp [Z]
    split_ifs with ho
    · have hd (i) (hi : i ∈ members p.1) : w i = w' i :=
        he i (by simp [WeightedConsistency.pairSupport,ho,hi])
      have hf (i) (hi : i ∈ members p.2) : w i = w' i :=
        he i (by simp [WeightedConsistency.pairSupport,ho,hi])
      rw [hd _ (firstUnit_mem _),hd _ (secondUnit_mem _),
        hf _ (firstUnit_mem _),hf _ (secondUnit_mem _)]
    · rfl
  have hbZ (N : ℕ) (a b : Fin k) (p : Dyad N × Dyad N) :
      ∀ᵐ w ∂P N, |Z N a b p w| ≤ B'^2 := by
    apply ae_of_all
    intro w
    dsimp [Z]
    split_ifs
    · rw [abs_mul,pow_two]
      exact mul_le_mul (hc _ a) (hc _ b) (abs_nonneg _) hB'
    · simp [sq_nonneg]
  have he (N : ℕ) (w : Fin N → U) (a b : Fin k) :
      F N w a b = ((N:ℝ)/(Dreal N)^2) * ∑ p, Z N a b p w := by
    simp only [F,meat,Matrix.sum_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,
      Fintype.sum_prod_type,Z,overlap,matrix_ite_apply,outer,Matrix.zero_apply,Pi.zero_apply]
    congr 1
  have hp (N : ℕ) (a b : Fin k) : MemLp (fun w => F N w a b) 2 (P N) := by
    simp_rw [he]
    have hz (p : Dyad N × Dyad N) : MemLp (Z N a b p) 2 (P N) :=
      MemLp.of_bound (hmZ N a b p).aestronglyMeasurable (B'^2) (hbZ N a b p)
    exact (memLp_finsetSum univ (fun p _ => hz p)).const_mul _
  have hv (a b : Fin k) : Tendsto (fun N => variance (fun w => F N w a b) (P N))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (6144*(B'^2)^2)/(N:ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
          Tendsto (fun N : ℕ => (6144*(B'^2)^2)*(N:ℝ)⁻¹) atTop (𝓝 ((6144*(B'^2)^2)*0)))
    apply squeeze_zero' (Eventually.of_forall (fun _ => variance_nonneg _ _)) _ ht
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp_rw [he]
    rw [variance_const_mul]
    have hh := (WeightedConsistency.g3_proof μ WeightedConsistency.pairSupport
      (Z N a b) (B'^2) (hmZ N a b) (hs N a b) (hbZ N a b)).trans
      (mul_le_mul_of_nonneg_left (WeightedConsistency.g4_proof N).2 (by positivity))
    calc
      _ ≤ ((N:ℝ)/(Dreal N)^2)^2*(24*(B'^2)^2*(N:ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        convert hh using 1 <;> first | rfl | ring
      _ = 24*(B'^2)^2*((N:ℝ)^7/(Dreal N)^4) := by ring
      _ ≤ 24*(B'^2)^2*(256/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (WeightedConsistency.meat_normalization_rate hN) (by positivity)
      _ = (6144*(B'^2)^2)/(N:ℝ) := by ring
  exact (WeightedConsistency.g5_proof P).1 F hp hv

/-- The multivariate Gaussian realizes the contrast definition. -/
theorem tb09_normalVectorLaw {k : ℕ} (M : Mat k) (hM : M.PosSemidef) :
    centeredNormalLaw (AronowAudit.P001.normalVectorLaw M) M := by
  refine ⟨hM,inferInstance,?_⟩
  intro c
  let z : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 c
  let L := innerSL ℝ z
  have hfun : (fun x : EuclideanSpace ℝ (Fin k) => dot c (fun j => x j)) = L := by
    ext x
    simp [L,z,dot,PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  have hm : (∫ x,L x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M)=0 := by
    change (∫ x,L (id x) ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M)=0
    rw [L.integral_comp_comm (IsGaussian.integrable_id)]
    simp only [id_eq,integral_id_multivariateGaussian]
    exact map_zero L
  have hv : variance L (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M) =
      dot c (M.mulVec c) := by
    change variance (fun u => inner ℝ z u) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M) = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id z,
      covarianceBilin_multivariateGaussian hM]
    rfl
  unfold AronowAudit.P001.normalVectorLaw
  rw [Measure.map_map (by unfold dot; fun_prop) (by fun_prop)]
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M).map
    (fun x => dot c (fun j => x j)) = _
  rw [hfun,IsGaussian.map_eq_gaussianReal,hm,hv]

theorem tb09_matrix_eq_of_quad {k : ℕ} (A B : Mat k)
    (hA : A.transpose=A) (hB : B.transpose=B)
    (h : ∀ c, dot c (A.mulVec c)=dot c (B.mulVec c)) : A=B := by
  classical
  ext i j
  change ∀ c,c ⬝ᵥ A *ᵥ c=c ⬝ᵥ B *ᵥ c at h
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hij := h (Pi.single i 1+Pi.single j 1)
  have ha : A j i=A i j := congrFun (congrFun hA i) j
  have hb : B j i=B i j := congrFun (congrFun hB i) j
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.col_apply] at hi hj hij
  linarith

theorem tb09_mean_outer_posSemidef {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (f : Ω → Vec k)
    (hp : ∀ a, MemLp (fun w => f w a) 2 μ) :
    (meanMat μ (fun w => outer (f w) (f w))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    simp only [Matrix.conjTranspose_apply,star_trivial,meanMat,outer]
    congr 1
    ext w
    ring
  · intro c
    change 0 ≤ dot c ((meanMat μ (fun w => outer (f w) (f w))).mulVec c)
    rw [GP0182B2b_mean_outer_quad μ f (fun a b => (hp a).integrable_mul (hp b))]
    exact integral_nonneg (fun _ => sq_nonneg _)

theorem tb09_pair_meat_mean {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (hm : Measurable h) (hp : ∀ j,MemLp (fun uv => h uv j) 2 (μ.prod μ))
    (hz : ∀ j,(∫ uv,h uv j ∂μ.prod μ)=0) (N : ℕ) :
    meanMat (Measure.pi (fun _ : Fin N => μ))
      (fun w => meat members (fun d => h (w (firstUnit d),w (secondUnit d)))) =
    varMat (Measure.pi (fun _ : Fin N => μ))
      (fun w => ∑ d : Dyad N,h (w (firstUnit d),w (secondUnit d))) := by
  classical
  let P := Measure.pi (fun _ : Fin N => μ)
  let q := fun (d : Dyad N) (w : Fin N → U) => h (w (firstUnit d),w (secondUnit d))
  have hq (d : Dyad N) (a : Fin k) : MemLp (fun w => q d w a) 2 P :=
    GP0182B2b_kernel_pair_memLp _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i) (hp a)
      (firstUnit_ne_secondUnit d)
  have hmean (d : Dyad N) : meanVec P (q d)=0 := by
    ext a
    change (∫ w,h (w (firstUnit d),w (secondUnit d)) a ∂P)=0
    exact (GP0182B2b_kernel_pair_integral _ (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i)
      ((measurable_pi_apply a).comp hm) (firstUnit_ne_secondUnit d)).trans (hz a)
  have hd (d f : Dyad N) (hdf : ¬(members d ∩ members f).Nonempty) :
      covMat P (q d) (q f)=0 := by
    ext a b
    exact WeightedConsistency.g2_proof μ (members d) (members f)
      (fun w => q d w a) (fun w => q f w b)
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hdf))
      ((measurable_pi_apply a).comp (tb09_pair_measurable h hm d))
      ((measurable_pi_apply b).comp (tb09_pair_measurable h hm f))
      (fun w w' he => by dsimp [q]; rw [he _ (firstUnit_mem d),he _ (secondUnit_mem d)])
      (fun w w' he => by dsimp [q]; rw [he _ (firstUnit_mem f),he _ (secondUnit_mem f)])
      (hq d a) (hq f b)
  rw [variance_sparse_identity P members q hq hmean hd]
  ext a b
  simp only [meanMat,meat,Matrix.sum_apply,matrix_ite_apply,outer,Matrix.zero_apply,Pi.zero_apply]
  have hi (d f : Dyad N) : Integrable (fun w =>
      if (members d ∩ members f).Nonempty then q d w a*q f w b else 0) P := by
    split_ifs
    · exact (hq d a).integrable_mul (hq f b)
    · exact integrable_const _
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun f _ => hi d f))]
  simp_rw [integral_finsetSum _ (fun f _ => hi _ f)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs <;> simp [q]

theorem tb09_pair_second_matrix {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (hm : Measurable h) (hp : ∀ j,MemLp (fun uv => h uv j) 2 (μ.prod μ))
    (hb : ∃ B : ℝ,∀ uv,‖h uv‖ ≤ B)
    (hsym : ∀ u v,h (u,v)=h (v,u))
    (hz : ∀ j,(∫ uv,h uv j ∂μ.prod μ)=0) {N : ℕ} (hN : 2 ≤ N) :
    let g := fun u j => ∫ v,h (u,v) j ∂μ
    varMat (Measure.pi (fun _ : Fin N => μ))
      (fun w => ∑ d : Dyad N,h (w (firstUnit d),w (secondUnit d))) =
    Dreal N • meanMat (μ.prod μ) (fun uv => outer (h uv) (h uv)) +
      ((N:ℝ)*((N:ℝ)-1)*((N:ℝ)-2)) • meanMat μ (fun u => outer (g u) (g u)) := by
  classical
  obtain ⟨B,hB⟩ := hb
  let P := Measure.pi (fun _ : Fin N => μ)
  let S := fun w : Fin N → U => ∑ d : Dyad N,h (w (firstUnit d),w (secondUnit d))
  let g := fun u j => ∫ v,h (u,v) j ∂μ
  have hg (j : Fin k) : MemLp (fun u => g u j) 2 μ :=
    (memLp_two_iff_integrable_sq (GP0182B2b_rowIntegral_measurable
      ((measurable_pi_apply j).comp hm)).aestronglyMeasurable).mpr
      (GP0182B2b_rowIntegral_sq_integrable (hp j))
  have hS (j : Fin k) : MemLp (fun w => S w j) 2 P := by
    simp only [S,Finset.sum_apply]
    exact memLp_finsetSum _ (fun d _ => GP0182B2b_kernel_pair_memLp _
      (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => measurePreserving_eval (fun _ : Fin N => μ) i) (hp j)
      (firstUnit_ne_secondUnit d))
  have hzero : meanVec P S=0 := by
    ext j
    simp only [meanVec,S,Finset.sum_apply,Pi.zero_apply]
    have hqi (d : Dyad N) : Integrable (fun w : Fin N → U =>
        h (w (firstUnit d),w (secondUnit d)) j) P :=
      (GP0182B2b_kernel_pair_memLp _ (iIndepFun_pi (fun _ => aemeasurable_id))
        (fun i => measurePreserving_eval (fun _ : Fin N => μ) i) (hp j)
        (firstUnit_ne_secondUnit d)).integrable one_le_two
    rw [integral_finsetSum _ (fun d _ => hqi d)]
    have he (d : Dyad N) : (∫ w : Fin N → U,
        h (w (firstUnit d),w (secondUnit d)) j ∂P)=0 := by
      exact (GP0182B2b_kernel_pair_integral _ (iIndepFun_pi (fun _ => aemeasurable_id))
        (fun i => measurePreserving_eval (fun _ : Fin N => μ) i)
        ((measurable_pi_apply j).comp hm) (firstUnit_ne_secondUnit d)).trans (hz j)
    simp only [he,Finset.sum_const_zero]
  rw [GP0182B2b_varMat_centered P S hS hzero]
  apply tb09_matrix_eq_of_quad
  · ext a b
    simp only [Matrix.transpose_apply,meanMat,outer]
    congr 1
    ext w
    ring
  · ext a b
    simp only [Matrix.transpose_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,meanMat,outer]
    congr 2 <;> congr 1 <;> ext w <;> ring
  · intro c
    let f := fun uv => dot c (h uv)
    have hf : MemLp f 2 (μ.prod μ) :=
      memLp_finsetSum _ (fun j _ => (hp j).const_mul (c j))
    have hf0 : (∫ uv,f uv ∂μ.prod μ)=0 := by
      dsimp only [f,dot]
      rw [integral_finsetSum _ (fun j _ => ((hp j).integrable one_le_two).const_mul _)]
      simp only [integral_const_mul,hz,mul_zero,Finset.sum_const_zero]
    have hrow (u : U) : GP0182B2b_rowIntegral (μ := μ) f u = dot c (g u) := by
      have hu (j) : Integrable (fun v => h (u,v) j) μ :=
        (MemLp.of_bound (((measurable_pi_apply j).comp hm).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
          (ae_of_all _ (fun v => (norm_le_pi_norm (h (u,v)) j).trans (hB _))) :
            MemLp _ 2 μ).integrable one_le_two
      simp only [f,dot,GP0182B2b_rowIntegral,g]
      rw [integral_finsetSum _ (fun j _ => (hu j).const_mul _)]
      simp only [integral_const_mul]
    have hsum (w : Fin N → U) : dot c (S w)=
        ∑ d : Dyad N,f (w (firstUnit d),w (secondUnit d)) := by
      simp only [S,f,dot,Finset.sum_apply,Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [GP0182B2b_mean_outer_quad P S (fun a b => (hS a).integrable_mul (hS b))]
    simp_rw [hsum]
    rw [GP0182B2b_dyad_second μ hN f (by unfold f dot; fun_prop) hf
      (fun u v => by dsimp [f]; rw [hsym u v]) hf0]
    simp_rw [hrow]
    simp only [Matrix.add_mulVec,GP0182B2b_dot_smul,Matrix.smul_mulVec]
    rw [show ∀ x y : Vec k,dot c (x+y)=dot c x+dot c y from fun x y => by
      simp [dot,mul_add,Finset.sum_add_distrib]]
    simp only [GP0182B2b_dot_smul]
    rw [GP0182B2b_mean_outer_quad (μ.prod μ) h (fun a b => (hp a).integrable_mul (hp b)),
      GP0182B2b_mean_outer_quad μ g (fun a b => (hg a).integrable_mul (hg b))]

theorem tb09_row_dot {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (hm : Measurable h) (hb : ∃ B : ℝ,∀ uv,‖h uv‖ ≤ B) (c : Vec k) (u : U) :
    (∫ v,dot c (h (u,v)) ∂μ)=dot c (fun j => ∫ v,h (u,v) j ∂μ) := by
  obtain ⟨B,hB⟩ := hb
  have hi (j) : Integrable (fun v => h (u,v) j) μ :=
    (MemLp.of_bound (((measurable_pi_apply j).comp hm).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
      (ae_of_all _ (fun v => (norm_le_pi_norm (h (u,v)) j).trans (hB _))) :
        MemLp _ 2 μ).integrable one_le_two
  simp only [dot]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  simp only [integral_const_mul]

theorem tb09_pair_vector_clt {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → Vec k)
    (hm : Measurable h) (hsym : ∀ u v,h (u,v)=h (v,u))
    (hb : ∃ B : ℝ,∀ uv,‖h uv‖ ≤ B)
    (hz : ∀ j,(∫ uv,h uv j ∂μ.prod μ)=0) :
    let g := fun u j => ∫ v,h (u,v) j ∂μ
    let Γ : Mat k := fun j l => ∫ u,g u j*g u l ∂μ
    ∃ G : Measure (Vec k),centeredNormalLaw G ((4:ℝ) • Γ) ∧
      weakLimit (fun N => Measure.pi (fun _ : Fin N => μ))
        (fun N w => (Real.sqrt N/Dreal N) •
          ∑ d : Dyad N,h (w (firstUnit d),w (secondUnit d))) G := by
  classical
  let g := fun u j => ∫ v,h (u,v) j ∂μ
  let Γ : Mat k := fun j l => ∫ u,g u j*g u l ∂μ
  let M := (4:ℝ) • Γ
  obtain ⟨B,hB⟩ := hb
  have hp (j : Fin k) : MemLp (fun uv => h uv j) 2 (μ.prod μ) :=
    tb09_pair_memLp μ _ ((measurable_pi_apply j).comp hm)
      (fun uv => (norm_le_pi_norm (h uv) j).trans (hB uv)) 2
  have hg (j : Fin k) : MemLp (fun u => g u j) 2 μ :=
    (memLp_two_iff_integrable_sq (GP0182B2b_rowIntegral_measurable
      ((measurable_pi_apply j).comp hm)).aestronglyMeasurable).mpr
      (GP0182B2b_rowIntegral_sq_integrable (hp j))
  have hM : M.PosSemidef := (tb09_mean_outer_posSemidef μ g hg).smul (by norm_num : (0:ℝ) ≤ 4)
  let P := fun N => Measure.pi (fun _ : Fin N => μ)
  let X := fun N (w : Fin N → U) => (Real.sqrt N/Dreal N) •
    ∑ d : Dyad N,h (w (firstUnit d),w (secondUnit d))
  let Z := fun N (w : Fin N → U) => WithLp.toLp 2 (X N w)
  have hXm (N : ℕ) : Measurable (X N) := by
    dsimp only [X]
    exact (measurable_const : Measurable (fun _ : Fin N → U => Real.sqrt N/Dreal N)).smul
      (Finset.measurable_fun_sum univ (fun d _ => tb09_pair_measurable h hm d))
  have hZm (N : ℕ) : Measurable (Z N) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (hXm N)
  have hd : TendstoInDistribution Z atTop id P
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) M) := by
    apply TendstoInDistribution.of_tendsto_charFun (fun N => (hZm N).aemeasurable)
      measurable_id.aemeasurable
    intro t
    let c : Vec k := fun j => t j
    let f := fun uv => dot c (h uv)
    have hfm : Measurable f := by unfold f dot; fun_prop
    have hfp : MemLp f 2 (μ.prod μ) :=
      memLp_finsetSum _ (fun j _ => (hp j).const_mul (c j))
    have hf0 : (∫ uv,f uv ∂μ.prod μ)=0 := by
      dsimp only [f,dot]
      rw [integral_finsetSum _ (fun j _ => ((hp j).integrable one_le_two).const_mul _)]
      simp only [integral_const_mul,hz,mul_zero,Finset.sum_const_zero]
    have hq : 4*(∫ u,(GP0182B2b_rowIntegral (μ := μ) f u)^2 ∂μ)=
        t ⬝ᵥ M *ᵥ t := by
      have he (u : U) : GP0182B2b_rowIntegral (μ := μ) f u=dot c (g u) :=
        tb09_row_dot μ h hm ⟨B,hB⟩ c u
      simp_rw [he]
      change _ = dot c (M.mulVec c)
      simp only [M,Matrix.smul_mulVec,GP0182B2b_dot_smul]
      rw [show dot c (Γ.mulVec c)=∫ u,(dot c (g u))^2 ∂μ from
        GP0182B2b_mean_outer_quad μ g (fun a b => (hg a).integrable_mul (hg b)) c]
    have hc := GP0182B2b_dyad_clt μ f hfm hfp
      (fun u v => by dsimp [f]; rw [hsym u v]) hf0
    have ht := hc.tendsto_charFun 1
    let Y := fun N (w : Fin N → U) => Real.sqrt N*GP0182B2b_dyadAverage f w
    have hYm (N : ℕ) : Measurable (Y N) :=
      (GP0182B2b_dyadAverage_measurable f hfm N).const_mul _
    have hlaw (N : ℕ) : (GP0182B2b_product μ).map
        (fun w => Y N (GP0182B2b_prefix N w))=(P N).map (Y N) := by
      change (GP0182B2b_product μ).map (Y N ∘ GP0182B2b_prefix N) = _
      rw [← Measure.map_map (hYm N) (GP0182B2b_prefix_measurable N),
        (GP0182B2b_prefix_preserving μ N).map_eq]
    change Tendsto (fun N => charFun ((GP0182B2b_product μ).map
      (fun w => Y N (GP0182B2b_prefix N w))) 1) atTop
      (𝓝 (charFun ((gaussianReal 0 (4*∫ u,(GP0182B2b_rowIntegral (μ := μ) f u)^2 ∂μ).toNNReal).map id) 1)) at ht
    simp_rw [hlaw] at ht
    have hproj (N : ℕ) : (fun w => inner ℝ (Z N w) t)=Y N := by
      ext w
      simp only [Z,X,PiLp.inner_apply,PiLp.toLp_apply,RCLike.inner_apply,
        conj_trivial,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Y,
        GP0182B2b_dyadAverage,f,dot,c,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [Finset.mul_sum,Finset.sum_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    have hnn : ((4*∫ u,(GP0182B2b_rowIntegral (μ := μ) f u)^2 ∂μ).toNNReal:ℝ)=
        t ⬝ᵥ M *ᵥ t := by
      rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _))),hq]
    simpa only [charFun_map_eq_charFun_map_inner_one (hZm _).aemeasurable,hproj,
      Measure.map_id,charFun_gaussianReal,charFun_multivariateGaussian hM,
      inner_zero_right,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,mul_zero,
      zero_sub,one_pow,mul_one,hnn,neg_div] using ht
  refine ⟨AronowAudit.P001.normalVectorLaw M,tb09_normalVectorLaw M hM,?_⟩
  refine ⟨fun N => (hXm N).aemeasurable,inferInstance,fun a => ?_⟩
  have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hd.forall_aemeasurable hd.aemeasurable_limit).1 hd
  have ha := ht (a.compContinuous ⟨(fun z : EuclideanSpace ℝ (Fin k) => fun j => z j),by fun_prop⟩)
  simpa only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    Z,PiLp.toLp_apply,id_eq,AronowAudit.P001.normalVectorLaw,
    integral_map (by fun_prop : AEMeasurable (fun z : EuclideanSpace ℝ (Fin k) => fun j => z j)
      (multivariateGaussian 0 M)) a.continuous.aestronglyMeasurable] using ha

/-- Bounded symmetric vector block scores: overlap-meat LLN and joint CLT. -/
theorem TailB_bounded_pair_score_limit
    {U : Type*} [MeasurableSpace U] {k : ℕ}
    (μ : Measure U) [IsProbabilityMeasure μ] (h : U × U → AronowAudit.P018.Vec k)
    (hm : Measurable h) (hsym : ∀ u v, h (u,v) = h (v,u))
    (hb : ∃ B : ℝ, ∀ uv, ‖h uv‖ ≤ B)
    (hz : ∀ j, (∫ uv, h uv j ∂(μ.prod μ)) = 0) :
    let g := fun u j => ∫ v, h (u,v) j ∂μ
    let Γ : AronowAudit.P018.Mat k := fun j l => ∫ u, g u j * g u l ∂μ
    let P := fun N => Measure.pi (fun _ : Fin N => μ)
    let H := fun N (w : Fin N → U) (d : AronowAudit.P018.Dyad N) =>
      h (w (AronowAudit.P018.firstUnit d), w (AronowAudit.P018.secondUnit d))
    AronowAudit.P018.inProbability P (fun N w =>
      ((N : ℝ) / (AronowAudit.P018.Dreal N)^2) •
        AronowAudit.P018.meat AronowAudit.P018.members (H N w) - (4 : ℝ) • Γ) ∧
    ∃ G : Measure (AronowAudit.P018.Vec k),
      AronowAudit.P018.centeredNormalLaw G ((4 : ℝ) • Γ) ∧
      AronowAudit.P018.weakLimit P (fun N w =>
        (Real.sqrt N / AronowAudit.P018.Dreal N) • ∑ d, H N w d) G := by
  classical
  let g := fun u j => ∫ v,h (u,v) j ∂μ
  let Γ : Mat k := fun j l => ∫ u,g u j*g u l ∂μ
  let S := meanMat (μ.prod μ) (fun uv => outer (h uv) (h uv))
  let P := fun N => Measure.pi (fun _ : Fin N => μ)
  let F := fun N (w : Fin N → U) => ((N:ℝ)/(Dreal N)^2) •
      meat members (fun d => h (w (firstUnit d),w (secondUnit d)))
  have hp (j : Fin k) : MemLp (fun uv => h uv j) 2 (μ.prod μ) := by
    obtain ⟨B,hB⟩ := hb
    exact tb09_pair_memLp μ _ ((measurable_pi_apply j).comp hm)
      (fun uv => (norm_le_pi_norm (h uv) j).trans (hB uv)) 2
  have hmean : Tendsto (fun N => meanMat (P N) (F N)) atTop (𝓝 ((4:ℝ) • Γ)) := by
    have ht := (GP0182B2b_NdivD_limit.smul (tendsto_const_nhds (x := S))).add
      (GP0182B2b_overlap_factor_limit.smul (tendsto_const_nhds (x := Γ)))
    simp only [zero_smul,zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    dsimp [F]
    rw [meanMat_scale,tb09_pair_meat_mean μ h hm hp hz,
      tb09_pair_second_matrix μ h hm hp hb hsym hz hN]
    simp only [smul_add,smul_smul]
    congr 1
    · congr 1
      field_simp [(printed_Dpos hN).ne']
    · congr 1
      ring
  constructor
  · have hh := WeightedConsistency.inProbability_add P
      (tb09_pair_meat_centered μ h hm hb)
      (WeightedConsistency.inProbability_deterministic P
        (fun N => meanMat (P N) (F N)-(4:ℝ) • Γ)
        (by convert hmean.sub_const ((4:ℝ) • Γ) using 1 <;> simp only [sub_self] <;> rfl))
    change inProbability P (fun N w => F N w-(4:ℝ) • Γ)
    change inProbability P (fun N w => (F N w-meanMat (P N) (F N))+
      (meanMat (P N) (F N)-(4:ℝ) • Γ)) at hh
    simpa only [sub_add_sub_cancel] using hh
  · exact tb09_pair_vector_clt μ h hm hsym hb hz

end AronowAudit.Shared.MapTailB
