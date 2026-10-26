import AronowAudit.P039.P039_Regression
import AronowAudit.External.Causalean.Stat.CLT.ChiSquaredProjection
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GaussianRatioMoments

namespace AronowAudit.P039.GaussianCompletion
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix RealInnerProductSpace NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- An actual coisometry maps standard Gaussian measure to standard Gaussian measure. -/
theorem gaussian_coisometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (hL : L ∘L L.adjoint = ContinuousLinearMap.id ℝ F) :
    (stdGaussian E).map L = stdGaussian F := by
  have hn (t : F) : ‖L.adjoint t‖^2=‖t‖^2 := by
    rw [← real_inner_self_eq_norm_sq,ContinuousLinearMap.adjoint_inner_left]
    have ht := congrArg (fun A : F →L[ℝ] F => A t) hL
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using
      congrArg (fun u => inner ℝ t u) ht
  apply Measure.ext_of_charFun
  funext t
  have hmap : charFun ((stdGaussian E).map L) t = charFun (stdGaussian E) (L.adjoint t) := by
    rw [charFun_apply,integral_map (by fun_prop) (by fun_prop),charFun_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hn' : ‖L.adjoint t‖=‖t‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hn t)
  rw [hmap,charFun_stdGaussian,charFun_stdGaussian,hn']

def matrixCLM {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  A.toEuclideanLin.toContinuousLinearMap

theorem matrixCLM_adjoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixCLM A).adjoint=matrixCLM Aᵀ := by
  unfold matrixCLM
  rw [← LinearMap.adjoint_toContinuousLinearMap,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]

theorem matrixCLM_coisometry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A*Aᵀ=1) :
    matrixCLM A ∘L (matrixCLM A).adjoint=ContinuousLinearMap.id ℝ _ := by
  rw [matrixCLM_adjoint]
  have hh := congrArg (Matrix.toLpLin 2 2) hA
  simp only [Matrix.toLpLin_mul_same,Matrix.toLpLin_one] at hh
  ext1 x
  exact congrArg (fun L => L x) hh

def contrastMatrix : Matrix (Fin 4) (Fin 6) ℝ :=
  !![0,0,1/Real.sqrt 2,-1/Real.sqrt 2,0,0;
     0,0,0,0,1/Real.sqrt 2,-1/Real.sqrt 2;
     1/2,1/2,-1/2,-1/2,0,0;
     1/(2*Real.sqrt 3),1/(2*Real.sqrt 3),1/(2*Real.sqrt 3),1/(2*Real.sqrt 3),-1/Real.sqrt 3,-1/Real.sqrt 3]

def contrasts (e : Fin 6 → ℝ) : Fin 4 → ℝ :=
  ![(e 2-e 3)/Real.sqrt 2,
    (e 4-e 5)/Real.sqrt 2,
    (e 0+e 1-e 2-e 3)/2,
    (e 0+e 1+e 2+e 3-2*e 4-2*e 5)/(2*Real.sqrt 3)]

theorem contrasts_matrix (e : Fin 6 → ℝ) : contrasts e=contrastMatrix *ᵥ e := by
  ext i
  fin_cases i <;> norm_num [contrasts,contrastMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem contrastMatrix_coisometry : contrastMatrix*contrastMatrixᵀ=1 := by
  have h2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hp2 := (Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)).ne'
  have hp3 := (Real.sqrt_pos.mpr (show (0:ℝ)<3 by norm_num)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [contrastMatrix,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

@[fun_prop] theorem contrasts_measurable : Measurable contrasts := by
  fun_prop [contrasts]

theorem contrasts_standard_law :
    (Measure.pi (fun _ : Fin 6 => gaussianReal 0 1)).map contrasts =
      Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin 6 => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)
  let L := matrixCLM contrastMatrix
  have hL : (stdGaussian (EuclideanSpace ℝ (Fin 6))).map L =
      stdGaussian (EuclideanSpace ℝ (Fin 4)) :=
    gaussian_coisometry L (matrixCLM_coisometry _ contrastMatrix_coisometry)
  have h6 : μ.map (WithLp.toLp 2)=stdGaussian (EuclideanSpace ℝ (Fin 6)) :=
    map_pi_eq_stdGaussian
  have h4 : ν.map (WithLp.toLp 2)=stdGaussian (EuclideanSpace ℝ (Fin 4)) :=
    map_pi_eq_stdGaussian
  have hof : (stdGaussian (EuclideanSpace ℝ (Fin 4))).map WithLp.ofLp=ν := by
    rw [← h4,Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def,WithLp.ofLp_toLp,Measure.map_id']
  have he : contrasts=WithLp.ofLp ∘ L ∘ WithLp.toLp 2 := by
    funext e
    rw [contrasts_matrix]
    rfl
  rw [he]
  change μ.map (WithLp.ofLp ∘ L ∘ WithLp.toLp 2)=ν
  rw [← Measure.map_map (by fun_prop : Measurable WithLp.ofLp)
      (by fun_prop : Measurable (L ∘ WithLp.toLp 2)),
    ← Measure.map_map (by fun_prop : Measurable L) (by fun_prop : Measurable (WithLp.toLp 2)),
    h6,hL,hof]

theorem normalize_gaussian (σ : ℝ≥0) (hσ : 0<σ) :
    (gaussianReal 0 (σ^2)).map (fun x => x/(σ:ℝ)) = gaussianReal 0 1 := by
  rw [gaussianReal_map_div_const]
  have he : NNReal.mk ((σ:ℝ)^2) (sq_nonneg (σ:ℝ))=σ^2 := by ext; rfl
  rw [he,div_self (pow_ne_zero 2 hσ.ne')]
  simp

theorem normalized_contrasts_law (σ : ℝ≥0) (hσ : 0<σ) :
    (Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
      (fun e => contrasts (fun i => e i/(σ:ℝ))) =
      Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
  have hn : (Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
      (fun e i => e i/(σ:ℝ))=Measure.pi (fun _ : Fin 6 => gaussianReal 0 1) := by
    have hmap := Measure.pi_map_pi (μ := fun _ : Fin 6 => gaussianReal 0 (σ^2))
      (f := fun (_ : Fin 6) (x : ℝ) => x/(σ:ℝ))
      (fun _ => (measurable_id.div_const (σ:ℝ)).aemeasurable)
    simpa only [normalize_gaussian σ hσ] using hmap
  calc
    _ = ((Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
        (fun e i => e i/(σ:ℝ))).map contrasts := by
      rw [Measure.map_map contrasts_measurable (by fun_prop)]
      rfl
    _ = _ := by rw [hn,contrasts_standard_law]


theorem standard_pair_squares (ν : ℕ) :
    (Measure.pi (fun _ : Fin (ν+1) => gaussianReal 0 1)).map
      (fun z => (z 0, ∑ i : Fin ν, (z i.succ)^2)) =
      (gaussianReal 0 1).prod (chiSquaredLaw ν) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (ν+1) => ℝ) 0
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (ν+1) => gaussianReal 0 1) 0).map_eq
  have hf : (fun z : Fin (ν+1) → ℝ => (z 0,∑ i : Fin ν,(z i.succ)^2)) =
      (Prod.map id (fun z : Fin ν → ℝ => ∑ i,z i^2)) ∘ e := by
    funext z
    simp [e,MeasurableEquiv.piFinSuccAbove_apply,Fin.succAbove_zero,Fin.tail]
  rw [hf,← Measure.map_map (by fun_prop) e.measurable,he]
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),Measure.map_id]
  rfl

theorem normalized_pair_law (σ : ℝ≥0) (hσ : 0<σ) :
    (Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
      (fun e => ((contrasts (fun i => e i/(σ:ℝ))) 0,
        ∑ i : Fin 3, ((contrasts (fun i => e i/(σ:ℝ))) i.succ)^2)) =
      (gaussianReal 0 1).prod (chiSquaredLaw 3) := by
  have he : (fun e : Fin 6 → ℝ => ((contrasts (fun i => e i/(σ:ℝ))) 0,
        ∑ i : Fin 3,((contrasts (fun i => e i/(σ:ℝ))) i.succ)^2)) =
      (fun z : Fin 4 → ℝ => (z 0,∑ i : Fin 3,(z i.succ)^2)) ∘
        (fun e => contrasts (fun i => e i/(σ:ℝ))) := rfl
  rw [he,← Measure.map_map (by fun_prop)
      (by fun_prop : Measurable (fun e : Fin 6 → ℝ => contrasts (fun i => e i/(σ:ℝ)))),
    normalized_contrasts_law σ hσ]
  exact standard_pair_squares 3


theorem raw_gram_inverse :
    ((residualLine witnessV)ᵀ*residualLine witnessV)⁻¹ = !![1/6,0;0,1/2] := by
  have hg : (residualLine witnessV)ᵀ*residualLine witnessV = !![(6:ℝ),0;0,2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [residualLine,witnessV,Matrix.mul_apply,Fin.sum_univ_succ]
  apply Matrix.inv_eq_left_inv
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]


def mean6 (e : Fin 6 → ℝ) : ℝ := (∑ i,e i)/6
def uc (e : Fin 6 → ℝ) : ℝ := (e 0-e 1)/2
def vc (e : Fin 6 → ℝ) : ℝ := (e 2-e 3)/2
def firstResidual (e : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => e i-mean6 e-uc e*witnessU i
def finalResidual (e : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => firstResidual e i-vc e*witnessV i

theorem first_candidate_residual (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    (witnessZ *ᵥ γ+e)-witnessZ *ᵥ ![γ 0+mean6 e,γ 1+uc e]=firstResidual e := by
  ext i
  norm_num [firstResidual,witnessZ,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem full_candidate_residual (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    (witnessZ *ᵥ γ+e)-(fullDesign witnessZ witnessV) *ᵥ
      ![γ 0+mean6 e,γ 1+uc e,vc e]=finalResidual e := by
  ext i
  norm_num [finalResidual,firstResidual,fullDesign,witnessZ,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem first_normal (e : Fin 6 → ℝ) : witnessZᵀ *ᵥ firstResidual e=0 := by
  ext j
  fin_cases j <;> norm_num [firstResidual,mean6,uc,witnessZ,witnessU,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem full_normal (e : Fin 6 → ℝ) : (fullDesign witnessZ witnessV)ᵀ *ᵥ finalResidual e=0 := by
  ext j
  fin_cases j <;> norm_num [finalResidual,firstResidual,mean6,uc,vc,fullDesign,
    witnessZ,witnessU,witnessV,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem first_residual_explicit (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsResidual witnessZ (witnessZ *ᵥ γ+e)=firstResidual e := by
  have hn : witnessZᵀ *ᵥ ((witnessZ *ᵥ γ+e)-
      witnessZ *ᵥ ![γ 0+mean6 e,γ 1+uc e])=0 := by
    rw [first_candidate_residual]
    exact first_normal e
  have hu := normal_equation_unique _ _ _ witness_baseline.2.2.1 hn
  have hc := hu.2 _ (full_rank_ols_unique _ _ witness_baseline.2.2.1).1
  unfold olsResidual
  rw [hc,first_candidate_residual]

theorem full_residual_explicit (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsResidual (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e)=finalResidual e := by
  have hA := full_orthogonal_witness_fit.1
  have hn : (fullDesign witnessZ witnessV)ᵀ *ᵥ ((witnessZ *ᵥ γ+e)-
      (fullDesign witnessZ witnessV) *ᵥ ![γ 0+mean6 e,γ 1+uc e,vc e])=0 := by
    rw [full_candidate_residual]
    exact full_normal e
  have hu := normal_equation_unique _ _ _ hA hn
  have hc := hu.2 _ (full_rank_ols_unique _ _ hA).1
  unfold olsResidual
  rw [hc,full_candidate_residual]

theorem residual_norm_contrasts (e : Fin 6 → ℝ) :
    squaredLength (finalResidual e)=∑ i : Fin 3,(contrasts e i.succ)^2 := by
  norm_num [finalResidual,firstResidual,mean6,uc,vc,witnessU,witnessV,contrasts,
    squaredLength,dotProduct,Fin.sum_univ_succ,div_pow,mul_pow,Real.sq_sqrt]
  ring

theorem full_sse_contrasts (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e) =
      ∑ i : Fin 3,(contrasts e i.succ)^2 := by
  unfold olsSSE
  rw [full_residual_explicit,residual_norm_contrasts]

theorem raw_candidate_residual (e : Fin 6 → ℝ) :
    firstResidual e-residualLine witnessV *ᵥ ![0,vc e]=finalResidual e := by
  ext i
  norm_num [finalResidual,residualLine,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem raw_normal (e : Fin 6 → ℝ) : (residualLine witnessV)ᵀ *ᵥ finalResidual e=0 := by
  ext j
  fin_cases j <;> norm_num [finalResidual,firstResidual,mean6,uc,vc,residualLine,
    witnessZ,witnessU,witnessV,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem raw_coefficients_explicit (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    ols (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) = ![0,vc e] := by
  have hA := residual_orthogonal_witness_fit.1
  rw [first_residual_explicit]
  have hn : (residualLine witnessV)ᵀ *ᵥ (firstResidual e-
      residualLine witnessV *ᵥ ![0,vc e])=0 := by
    rw [raw_candidate_residual]
    exact raw_normal e
  exact (normal_equation_unique _ _ _ hA hn).2 _ (full_rank_ols_unique _ _ hA).1

theorem raw_coefficient_contrast (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    ols (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1 =
      (e 2-e 3)/2 := by
  rw [raw_coefficients_explicit]
  rfl

theorem raw_sse_contrasts (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsSSE (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) =
      ∑ i : Fin 3,(contrasts e i.succ)^2 := by
  unfold olsSSE
  change squaredLength (olsResidual witnessZ (witnessZ *ᵥ γ+e)-
    residualLine witnessV *ᵥ ols (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)))=_
  rw [raw_coefficients_explicit,first_residual_explicit,raw_candidate_residual,
    residual_norm_contrasts]

theorem raw_se_contrasts (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsSESquared (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1 =
      (∑ i : Fin 3,(contrasts e i.succ)^2)/8 := by
  unfold olsSESquared
  rw [raw_sse_contrasts,raw_gram_inverse]
  norm_num
  ring

theorem normalized_contrasts (σ : ℝ) (e : Fin 6 → ℝ) :
    contrasts (fun i => e i/σ) = fun i => contrasts e i/σ := by
  ext i
  fin_cases i <;> norm_num [contrasts] <;> ring

 theorem scalar_scaled_stat (c s σ : ℝ) (hσ : 0<σ) :
    (c/2)/Real.sqrt (s/8) =
      (c/(σ*Real.sqrt 2))/Real.sqrt ((s/σ^2)/4) := by
  have h8 : Real.sqrt (8:ℝ)=2*Real.sqrt 2 := by
    rw [show (8:ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  have hsσ : Real.sqrt (σ^2*4)=σ*2 := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hσ.le]
    norm_num
  rw [show (s/σ^2)/4=s/(σ^2*4) by ring,Real.sqrt_div' _ (by norm_num : (0:ℝ)≤8),h8,
    Real.sqrt_div' _ (by positivity : (0:ℝ)≤σ^2*4),hsσ]
  by_cases hs : Real.sqrt s=0
  · simp [hs]
  · have h2 := (Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)).ne'
    field_simp
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]

theorem dot_witnessV (e : Fin 6 → ℝ) : dotProduct witnessV e=e 2-e 3 := by
  norm_num [witnessV,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_pair_law (σ : ℝ≥0) (hσ : 0<σ) (γ : Fin 2 → ℝ) :
    (Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
      (fun e => (dotProduct witnessV e/((σ:ℝ)*Real.sqrt 2),
        olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e)/(σ:ℝ)^2)) =
      (gaussianReal 0 1).prod (chiSquaredLaw 3) := by
  have he : (fun e : Fin 6 → ℝ => (dotProduct witnessV e/((σ:ℝ)*Real.sqrt 2),
      olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e)/(σ:ℝ)^2)) =
      (fun e => (contrasts (fun i => e i/(σ:ℝ)) 0,
        ∑ i : Fin 3,(contrasts (fun i => e i/(σ:ℝ)) i.succ)^2)) := by
    funext e
    apply Prod.ext
    · rw [dot_witnessV]
      norm_num [contrasts]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · rw [full_sse_contrasts,normalized_contrasts]
      simp only [div_pow,Finset.sum_div]
  rw [he]
  exact normalized_pair_law σ hσ

theorem actual_stat_ratio (σ : ℝ≥0) (hσ : 0<σ) (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    olsT (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1 =
      (dotProduct witnessV e/((σ:ℝ)*Real.sqrt 2))/Real.sqrt
        ((olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e)/(σ:ℝ)^2)/4) := by
  unfold olsT
  rw [raw_coefficient_contrast,raw_se_contrasts,full_sse_contrasts,dot_witnessV]
  exact scalar_scaled_stat _ _ (σ:ℝ) (by exact_mod_cast hσ)

theorem actual_coordinates (σ : ℝ) (γ : Fin 2 → ℝ) (e : Fin 6 → ℝ) :
    dotProduct witnessV e/(σ*Real.sqrt 2)=contrasts (fun i => e i/σ) 0 ∧
    olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ+e)/σ^2=
      ∑ i : Fin 3,(contrasts (fun i => e i/σ) i.succ)^2 := by
  constructor
  · rw [dot_witnessV]
    norm_num [contrasts]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [full_sse_contrasts,normalized_contrasts]
    simp only [div_pow,Finset.sum_div]

def ratioFour (z : Fin 4 → ℝ) : ℝ := z 0/Real.sqrt ((∑ i : Fin 3,(z i.succ)^2)/4)

@[fun_prop] theorem ratioFour_measurable : Measurable ratioFour := by fun_prop [ratioFour]

theorem erase_zero_sum {ν : ℕ} (z : Fin (ν+1) → ℝ) :
    (∑ i ∈ Finset.univ.erase (0:Fin (ν+1)),(z i)^2)=∑ i : Fin ν,(z i.succ)^2 := by
  have ha := Fin.sum_univ_succ (fun i : Fin (ν+1) => (z i)^2)
  have hb := Finset.sum_erase_add Finset.univ (fun i : Fin (ν+1) => (z i)^2)
    (Finset.mem_univ (0:Fin (ν+1)))
  linarith

theorem ratio_four_law :
    (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)).map ratioFour =
      (studentLaw 3).map (fun t => Real.sqrt (4/3:ℝ)*t) := by
  unfold studentLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with z
  dsimp only [Function.comp_apply,ratioFour]
  rw [erase_zero_sum]
  let S := ∑ i : Fin 3,(z i.succ)^2
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change z 0/Real.sqrt (S/4)=Real.sqrt (4/3:ℝ)*(z 0/Real.sqrt (S/3))
  by_cases hs : S=0
  · simp [hs]
  · exact RegressionCompletion.signed_t_scale (z 0) S 4 3
      (lt_of_le_of_ne hS (Ne.symm hs)) (by norm_num) (by norm_num)

theorem actual_stat_function (σ : ℝ≥0) (hσ : 0<σ) (γ : Fin 2 → ℝ) :
    (fun e => olsT (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1)=
      ratioFour ∘ (fun e => contrasts (fun i => e i/(σ:ℝ))) := by
  funext e
  rw [actual_stat_ratio σ hσ γ e]
  rw [(actual_coordinates (σ:ℝ) γ e).1,(actual_coordinates (σ:ℝ) γ e).2]
  rfl

@[fun_prop] theorem actual_stat_measurable (σ : ℝ≥0) (hσ : 0<σ) (γ : Fin 2 → ℝ) :
    Measurable (fun e => olsT (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1) := by
  rw [actual_stat_function σ hσ γ]
  fun_prop [contrasts]

theorem actual_stat_law (σ : ℝ≥0) (hσ : 0<σ) (γ : Fin 2 → ℝ) :
    (Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))).map
      (fun e => olsT (residualLine witnessV) (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1)=
      (studentLaw 3).map (fun t => Real.sqrt (4/3:ℝ)*t) := by
  rw [actual_stat_function σ hσ γ,
    ← Measure.map_map ratioFour_measurable
      (by fun_prop [contrasts] : Measurable (fun e : Fin 6 → ℝ => contrasts (fun i => e i/(σ:ℝ)))),
    normalized_contrasts_law σ hσ,ratio_four_law]

theorem student_three_second_moment : (∫ t : ℝ,t^2 ∂studentLaw 3)=3 := by
  simpa only [studentLaw,Nat.cast_ofNat,show (3:ℝ)/(3-2)=3 by norm_num] using
    (AronowAudit.GaussianCompletion.gaussian_ratio_law_second_moment (ν:=3) (by norm_num))

theorem student_four_second_moment : (∫ t : ℝ,t^2 ∂studentLaw 4)=2 := by
  simpa only [studentLaw,Nat.cast_ofNat,show (4:ℝ)/(4-2)=2 by norm_num] using
    (AronowAudit.GaussianCompletion.gaussian_ratio_law_second_moment (ν:=4) (by norm_num))

theorem scaled_student_three_second_moment :
    (∫ t : ℝ,t^2 ∂(studentLaw 3).map (fun s => Real.sqrt (4/3:ℝ)*s))=4 := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,Real.sq_sqrt (show (0:ℝ)≤4/3 by norm_num)]
  rw [integral_const_mul,student_three_second_moment]
  norm_num

theorem residual_gaussian_reference_completed (σ : ℝ≥0) (hσ : 0 < σ)
    (γ : Fin 2 → ℝ) :
    let μ := Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))
    let stat := fun ε => olsT (residualLine witnessV)
      (olsResidual witnessZ (witnessZ *ᵥ γ + ε)) 1
    let U := fun ε => dotProduct witnessV ε / ((σ : ℝ)*Real.sqrt 2)
    let V := fun ε => olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ + ε) / (σ : ℝ)^2
    μ.map (fun ε => (U ε, V ε)) = (gaussianReal 0 1).prod (chiSquaredLaw 3) ∧
    (∀ ε, stat ε = U ε / Real.sqrt (V ε/4)) ∧
    μ.map stat = (studentLaw 3).map (fun t => Real.sqrt (4/3 : ℝ)*t) ∧
    (∫ ε, (stat ε)^2 ∂μ) = 4 ∧ (∫ t, t^2 ∂studentLaw 3) = 3 ∧
    (∫ t, t^2 ∂studentLaw 4) = 2 ∧
    μ.map stat ≠ studentLaw 4 := by
  dsimp only
  let μ := Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))
  let stat := fun e => olsT (residualLine witnessV)
    (olsResidual witnessZ (witnessZ *ᵥ γ+e)) 1
  have hlaw : μ.map stat=(studentLaw 3).map (fun t => Real.sqrt (4/3:ℝ)*t) :=
    actual_stat_law σ hσ γ
  have hmapped : (∫ t : ℝ,t^2 ∂μ.map stat)=4 := by
    rw [hlaw]
    exact scaled_student_three_second_moment
  have hmoment : (∫ e,(stat e)^2 ∂μ)=4 := by
    have hi := integral_map (μ:=μ) (φ:=stat)
      (actual_stat_measurable σ hσ γ).aemeasurable
      (show AEStronglyMeasurable (fun t : ℝ => t^2) (μ.map stat) by fun_prop)
    exact hi.symm.trans hmapped
  refine ⟨actual_pair_law σ hσ γ,actual_stat_ratio σ hσ γ,hlaw,hmoment,
    student_three_second_moment,student_four_second_moment,?_⟩
  intro he
  rw [he] at hmapped
  linarith [student_four_second_moment]

end
end AronowAudit.P039.GaussianCompletion
namespace AronowAudit.P039
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal

/-- T3(v): for the concrete full-rank witness and any positive Gaussian
noise scale under the conditional null, the residual-line statistic has the
scaled t3 law, its second moment is four, whereas t4 has second moment two.
The laws differ. This is a distributional statement, separate from the
sample counterexample and the analytic-tail definitions. -/
theorem residual_gaussian_reference_counterexample (σ : ℝ≥0) (hσ : 0 < σ)
    (γ : Fin 2 → ℝ) :
    let μ := Measure.pi (fun _ : Fin 6 => gaussianReal 0 (σ^2))
    let stat := fun ε => olsT (residualLine witnessV)
      (olsResidual witnessZ (witnessZ *ᵥ γ + ε)) 1
    let U := fun ε => dotProduct witnessV ε / ((σ : ℝ)*Real.sqrt 2)
    let V := fun ε => olsSSE (fullDesign witnessZ witnessV) (witnessZ *ᵥ γ + ε) / (σ : ℝ)^2
    μ.map (fun ε => (U ε, V ε)) = (gaussianReal 0 1).prod (chiSquaredLaw 3) ∧
    (∀ ε, stat ε = U ε / Real.sqrt (V ε/4)) ∧
    μ.map stat = (studentLaw 3).map (fun t => Real.sqrt (4/3 : ℝ)*t) ∧
    (∫ ε, (stat ε)^2 ∂μ) = 4 ∧ (∫ t, t^2 ∂studentLaw 3) = 3 ∧
    (∫ t, t^2 ∂studentLaw 4) = 2 ∧
    μ.map stat ≠ studentLaw 4 := by
  exact GaussianCompletion.residual_gaussian_reference_completed σ hσ γ

end AronowAudit.P039
