import AronowAudit.P018.Wave1.Gap.TailBSignProbability
import AronowAudit.P001.Wave1.Gap.DecideB

/-! Joint Gaussian limit of the two sign sums needed by the slope expansion. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

local instance tb05_inference_unit_probability : IsProbabilityMeasure signPairKernel.μ := tb05_standing.1

def tb05_vec (u : Bool × Bool) : Vec 2 := ![signValue u.1,signValue u.1*signValue u.2]
def tb05_pairStatistic (N : ℕ) (ω : Fin N → Bool × Bool) : Vec 2 :=
  ![(∑ i,tb05_z ω i)/Real.sqrt N,(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N]

theorem tb05_vec_mean (j : Fin 2) : (∫ u,tb05_vec u j ∂signPairKernel.μ)=0 := by
  rw [tb05_unit_integral]
  fin_cases j <;> norm_num [tb05_average,tb05_vec,signValue]

theorem tb05_vec_second (j k : Fin 2) :
    (∫ u,tb05_vec u j*tb05_vec u k ∂signPairKernel.μ)=(1:Mat 2) j k := by
  rw [tb05_unit_integral]
  fin_cases j <;> fin_cases k <;> norm_num [tb05_average,tb05_vec,signValue,Matrix.one_apply]

theorem tb05_standard_vector_law : AronowAudit.P001.normalVectorLaw (1:Mat 2) =
    Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) := by
  unfold AronowAudit.P001.normalVectorLaw
  rw [multivariateGaussian_zero_one,← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (PiLp.continuous_toLp 2 _).measurable]
  change (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map id = _
  exact Measure.map_id

theorem tb05_joint_sign_clt :
    weakLimit (unitSampleLaw signPairKernel) tb05_pairStatistic
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
  let μ := signPairKernel.μ
  let P := GP0182B2b_product μ
  let s : ℕ → (ℕ → Bool × Bool) → Vec 2 := fun i ω => tb05_vec (ω i)
  have hm : Measurable tb05_vec := measurable_of_countable _
  have hid (i : ℕ) : IdentDistrib (s i) tb05_vec P μ := by
    refine ⟨(hm.comp (measurable_pi_apply i)).aemeasurable,hm.aemeasurable,?_⟩
    change P.map (tb05_vec ∘ (fun ω => ω i)) = _
    rw [← Measure.map_map hm (measurable_pi_apply i)]
    congr 1
    exact Measure.infinitePi_map_eval _ _
  have hiid : AronowAudit.P001.IID P s :=
    ⟨fun i => hm.comp (measurable_pi_apply i),
      iIndepFun_infinitePi (P := fun _ : ℕ => μ) (fun _ => hm),
      fun i => (hid i).trans (hid 0).symm⟩
  have h2 (j : Fin 2) : MemLp (fun ω => s 0 ω j) 2 P := by
    exact (GP0182B2b_iid_ident μ (fun u => tb05_vec u j) (measurable_of_countable _) 0).memLp_iff.mpr
      (printed_finite_L2 μ _)
  have h0 (j : Fin 2) : AronowAudit.P001.mean P (fun ω => s 0 ω j)=0 := by
    change (∫ ω,tb05_vec (ω 0) j ∂P)=0
    rw [(GP0182B2b_iid_ident μ (fun u => tb05_vec u j) (measurable_of_countable _) 0).integral_eq]
    exact tb05_vec_mean j
  have hcov (j k : Fin 2) : (1:Mat 2) j k=
      AronowAudit.P001.mean P (fun ω => s 0 ω j*s 0 ω k) := by
    change (1:Mat 2) j k=(∫ ω,tb05_vec (ω 0) j*tb05_vec (ω 0) k ∂P)
    rw [(GP0182B2b_iid_ident μ (fun u => tb05_vec u j*tb05_vec u k)
      (measurable_of_countable _) 0).integral_eq]
    exact (tb05_vec_second j k).symm
  have hd := AronowAudit.P001.Wave1.DecideB_vector_clt_distribution P s hiid h2 h0
    (1:Mat 2) Matrix.PosSemidef.one hcov
  have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hd.forall_aemeasurable hd.aemeasurable_limit).1 hd
  simp only [tb05_standard_vector_law] at ht
  have he (N : ℕ) (ω : ℕ → Bool × Bool) :
      (Real.sqrt N)⁻¹ • (fun j => ∑ i ∈ Finset.range N,s i ω j) =
      tb05_pairStatistic N (GP0182B2b_prefix N ω) := by
    ext j
    fin_cases j <;>
      simp [s,tb05_vec,tb05_pairStatistic,tb05_z,tb05_w,GP0182B2b_prefix,
        ← Fin.sum_univ_eq_sum_range,div_eq_mul_inv,mul_comm]
  refine ⟨fun N => (measurable_of_countable _).aemeasurable,inferInstance,?_⟩
  intro g
  have hp (N : ℕ) : (∫ ω,g (tb05_pairStatistic N (GP0182B2b_prefix N ω)) ∂P)=
      ∫ ω,g (tb05_pairStatistic N ω) ∂unitSampleLaw signPairKernel N :=
    GP0182B2b_prefix_integral μ N (fun ω => g (tb05_pairStatistic N ω)) (measurable_of_countable _)
  simpa only [he,hp,id_eq] using ht g


def tb05_quadraticMap (z : ℝ × ℝ) : ℝ := 4*(z.1^2+z.2^2-1)
def tb05_quadraticLaw : Measure ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map tb05_quadraticMap
def tb05_quadraticStatistic (N : ℕ) (ω : Fin N → Bool × Bool) : ℝ :=
  4*(((∑ i,tb05_z ω i)/Real.sqrt N)^2+
    ((∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N)^2-1)

theorem tb05_quadratic_limit :
    weakLimit (unitSampleLaw signPairKernel) tb05_quadraticStatistic tb05_quadraticLaw := by
  have hp := AronowAudit.Shared.MapTailB.TailB_weakLimit_continuous_map
    (unitSampleLaw signPairKernel) tb05_pairStatistic _ tb05_joint_sign_clt
    (fun z : Vec 2 => (z 0,z 1)) (by fun_prop)
  have hlaw : (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
      (fun z : Vec 2 => (z 0,z 1)) = (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [hlaw] at hp
  have hq := AronowAudit.Shared.MapTailB.TailB_weakLimit_continuous_map
    (unitSampleLaw signPairKernel) _ _ hp tb05_quadraticMap (by unfold tb05_quadraticMap; fun_prop)
  dsimp only [tb05_pairStatistic,tb05_quadraticMap,tb05_quadraticStatistic,tb05_quadraticLaw] at hq ⊢
  exact hq

theorem tb05_quadratic_law_mass :
    (tb05_quadraticLaw (Set.Iio 0)).toReal=1-Real.exp (-1/2) ∧ tb05_quadraticLaw {0}=0 := by
  obtain ⟨hm,hz⟩ := AronowAudit.Shared.MapTailB.TailB_gaussian_disk
  let G := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have h1 : tb05_quadraticLaw (Set.Iio 0)=G {z : ℝ × ℝ | z.1^2+z.2^2<1} := by
    rw [tb05_quadraticLaw,Measure.map_apply (by unfold tb05_quadraticMap; fun_prop) measurableSet_Iio]
    congr 1
    ext z
    change 4*(z.1^2+z.2^2-1)<0 ↔ z.1^2+z.2^2<1
    constructor <;> intro h <;> linarith
  have h0 : tb05_quadraticLaw {0}=G {z : ℝ × ℝ | z.1^2+z.2^2=1} := by
    rw [tb05_quadraticLaw,Measure.map_apply (by unfold tb05_quadraticMap; fun_prop)
      (measurableSet_singleton 0)]
    congr 1
    ext z
    change 4*(z.1^2+z.2^2-1)=0 ↔ z.1^2+z.2^2=1
    constructor <;> intro h <;> linarith
  rw [h1,h0]
  exact ⟨hm,hz⟩


theorem tb05_scaled_slope_weak :
    weakLimit (unitSampleLaw signPairKernel) (fun N ω =>
      (N:ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1)
      tb05_quadraticLaw := by
  apply AronowAudit.Shared.MapTailB.TailB_weakLimit_perturbation
    (unitSampleLaw signPairKernel) tb05_quadraticStatistic _ _ tb05_quadratic_limit
    (fun _ => (measurable_of_countable _).aemeasurable)
  intro ε hε
  simpa only [tb05_secondOrderError,tb05_quadraticStatistic,Real.norm_eq_abs,abs_sub_comm] using
    tb05_second_order_in_probability ε hε

theorem tb05_negative_variance_probability :
    Tendsto (fun N : ℕ => (unitSampleLaw signPairKernel N {ω |
      sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1<0}).toReal)
      atTop (𝓝 (1-Real.exp (-1/2))) := by
  have hl := AronowAudit.Shared.MapTailB.TailB_weakLimit_Iio
    (unitSampleLaw signPairKernel) _ _ tb05_scaled_slope_weak 0 tb05_quadratic_law_mass.2
  rw [tb05_quadratic_law_mass.1] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0:ℝ) < (N:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast (by omega : 0 < N))
  have he : {ω : Fin N → Bool × Bool | (N:ℝ)^2*
      sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1<0} =
      {ω | sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1<0} := by
    ext ω
    change (N:ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1<0 ↔
      sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1<0
    rw [mul_neg_iff]
    simp [hn,not_lt_of_ge hn.le]
  rw [he]

theorem tb05_pivot_not_normal :
    ¬weakLimit (unitSampleLaw signPairKernel) (fun N ω => coefficientError signPairKernel ω 1 /
      Real.sqrt (sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1))
      (gaussianReal 0 1) := by
  have hc : (0:ℝ) < 1-Real.exp (-1/2) := by
    have he : Real.exp (-1/2)<1 := Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  exact AronowAudit.Shared.MapTailB.TailB_no_gaussian_limit_negative_variance
    (unitSampleLaw signPairKernel) (fun N ω => coefficientError signPairKernel ω 1)
    (fun N ω => sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1)
    _ hc tb05_negative_variance_probability

end AronowAudit.P018.Wave1.TailBSign
