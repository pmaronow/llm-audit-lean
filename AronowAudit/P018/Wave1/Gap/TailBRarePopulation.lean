import AronowAudit.P018.Wave1.Gap.TailBRareFinite
import AronowAudit.Shared.MapTailB.BoundedPairScore

/-! Population calculations for the original rare-category construction. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.Shared.MapTailB
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

local instance tb09_rare_population_probability : IsProbabilityMeasure rareLaw := TailB_rare_probability

theorem tb09_rare_integrable (f : RareUnit → ℝ) (hb : ∃ B : ℝ, ∀ u, |f u| ≤ B) :
    Integrable f rareLaw := by
  obtain ⟨B,hB⟩ := hb
  exact (MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable B
    (ae_of_all _ hB) : MemLp f 2 rareLaw).integrable one_le_two

theorem tb09_rare_integral (f : RareUnit → ℝ) (hi : Integrable f rareLaw) :
    (∫ u,f u ∂rareLaw)=∑' m : ℕ,TailB_rare_p m *
      (∑ c : Fin (m+1),∑ a : Bool,∑ b : Bool,f ⟨m,c,a,b⟩) := by
  rw [rareLaw,integral_sum_measure hi]
  congr 1
  ext m
  rw [integral_smul_measure]
  simp only [show ((2:ℝ)^(-(m+1:ℤ))/((m+1:ℝ)*4))=TailB_rare_p m from rfl,
    ENNReal.toReal_ofReal (TailB_rare_p_pos m).le,smul_eq_mul]
  congr 1
  rw [integral_finsetSum_measure (fun c _ => by
    simp [integrable_finsetSum_measure,integrable_dirac])]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_finsetSum_measure (fun a _ => by
    simp [integrable_finsetSum_measure,integrable_dirac])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum_measure (fun b _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem tb09_rare_sign_mean (A : Bool) :
    (∫ u,signValue (if A then u.A else u.B) ∂rareLaw)=0 := by
  rw [tb09_rare_integral _ (tb09_rare_integrable _ ⟨1,fun u => by
    rw [TailB_rare_sign_abs]⟩)]
  cases A <;> simp [Fintype.sum_bool,signValue]

theorem tb09_rare_s_symmetric (u v : RareUnit) : rareS u v=rareS v u := by
  by_cases hs : rareSmall u v
  · have hv := (TailB_rare_small_symm u v).mp hs
    simp only [rareS,hs,hv,if_true]
    rw [hs.1]
  · have hv : ¬rareSmall v u := fun h => hs ((TailB_rare_small_symm u v).mpr h)
    simp [rareS,hs,hv]

theorem tb09_rare_a_symmetric (u v : RareUnit) : rareA u v=rareA v u := by
  by_cases hs : rareSmall u v
  · have hv := (TailB_rare_small_symm u v).mp hs
    simp [rareA,hs,hv,add_comm]
  · have hv : ¬rareSmall v u := fun h => hs ((TailB_rare_small_symm u v).mpr h)
    simp [rareA,hs,hv]

def tb09_rare_W (uv : RareUnit × RareUnit) : ℝ := rareS uv.1 uv.2 * rareA uv.1 uv.2
def tb09_rare_h (m : ℕ) : ℝ :=
  (2:ℝ)^(-(m+1:ℤ))*(1-1/(m+1:ℝ))*rareDelta (m+1)

theorem tb09_rare_W_bound (uv : RareUnit × RareUnit) : |tb09_rare_W uv| ≤ 2 := by
  rw [tb09_rare_W,abs_mul,abs_of_pos (TailB_rare_s_bounds _ _).1]
  calc
    _ ≤ 1*2 := mul_le_mul (TailB_rare_s_bounds _ _).2 (TailB_rare_a_bound _ _)
      (abs_nonneg _) (by norm_num)
    _ = 2 := by ring

theorem tb09_rare_W_symmetric (u v : RareUnit) : tb09_rare_W (u,v)=tb09_rare_W (v,u) := by
  simp only [tb09_rare_W,tb09_rare_s_symmetric u v,tb09_rare_a_symmetric u v]

theorem tb09_rare_W_row (u : RareUnit) :
    (∫ v,tb09_rare_W (u,v) ∂rareLaw)=signValue u.A*tb09_rare_h u.m := by
  rw [tb09_rare_integral _ (tb09_rare_integrable _ ⟨2,fun v => tb09_rare_W_bound (u,v)⟩)]
  rw [tsum_eq_single u.m]
  · have hc (c : Fin (u.m+1)) :
        (∑ a : Bool,∑ b : Bool,tb09_rare_W (u,⟨u.m,c,a,b⟩))=
        if c=u.label then 0 else 4*rareDelta (u.m+1)*signValue u.A := by
      by_cases he : c=u.label
      · subst c
        simp [tb09_rare_W,rareS,rareA,rareSmall]
      · have he' : u.label.val ≠ c.val := fun hh => he (Fin.ext hh.symm)
        cases hA : u.A <;>
          simp [tb09_rare_W,rareS,rareA,rareSmall,he',he,hA,Fintype.sum_bool,signValue] <;> ring
    simp_rw [hc]
    have hs : (∑ c : Fin (u.m+1),if c=u.label then (0:ℝ) else
        4*rareDelta (u.m+1)*signValue u.A)=
        (u.m:ℝ)*(4*rareDelta (u.m+1)*signValue u.A) := by
      simp [sum_ite,Finset.filter_ne',Finset.sum_const,Finset.card_erase_of_mem]
    rw [hs]
    dsimp [TailB_rare_p,tb09_rare_h]
    have hne : (u.m+1:ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  · intro m hm
    have he : u.m ≠ m := Ne.symm hm
    simp [tb09_rare_W,rareS,rareA,rareSmall,he]

theorem tb09_rare_h_bounds (m : ℕ) : 0 ≤ tb09_rare_h m ∧ tb09_rare_h m ≤ 1 := by
  have hm : (1:ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hp : 0 < (2:ℝ)^(-(m+1:ℤ)) := by positivity
  have hp1 : (2:ℝ)^(-(m+1:ℤ)) ≤ 1 := by
    rw [show -(m+1:ℤ)=-((m+1:ℕ):ℤ) by omega,_root_.zpow_neg,zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ht : 0 ≤ 1-1/(m+1:ℝ) := by
    apply sub_nonneg.mpr
    simpa only [one_div,inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hm
  have ht1 : 1-1/(m+1:ℝ) ≤ 1 := sub_le_self _ (by positivity)
  constructor
  · exact mul_nonneg (mul_nonneg hp.le ht) (TailB_rare_delta_pos _ (by omega)).le
  · calc
      _ ≤ 1*1*1 := mul_le_mul (mul_le_mul hp1 ht1 ht (by norm_num))
        (TailB_rare_delta_le_one _ (by omega))
        (TailB_rare_delta_pos _ (by omega)).le (by norm_num)
      _ = 1 := by ring

def tb09_rare_Z (u : RareUnit) : ℝ := signValue u.A*tb09_rare_h u.m

theorem tb09_rare_Z_bound (u : RareUnit) : |tb09_rare_Z u| ≤ 1 := by
  rw [tb09_rare_Z,abs_mul,TailB_rare_sign_abs,one_mul,
    abs_of_nonneg (tb09_rare_h_bounds _).1]
  exact (tb09_rare_h_bounds _).2

theorem tb09_rare_Z_mean : (∫ u,tb09_rare_Z u ∂rareLaw)=0 := by
  rw [tb09_rare_integral _ (tb09_rare_integrable _ ⟨1,tb09_rare_Z_bound⟩)]
  simp [tb09_rare_Z,Fintype.sum_bool,signValue,← Finset.sum_add_distrib]

theorem tb09_rare_Z_square : (∫ u,(tb09_rare_Z u)^2 ∂rareLaw)=rareH := by
  have hi : Integrable (fun u => (tb09_rare_Z u)^2) rareLaw :=
    tb09_rare_integrable _ ⟨1,fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (tb09_rare_Z_bound u)⟩
  rw [tb09_rare_integral _ hi]
  unfold rareH
  congr 1
  ext m
  have hs (a b : Bool) : (tb09_rare_Z ⟨m,(0:Fin (m+1)),a,b⟩)^2=(tb09_rare_h m)^2 := by
    simp only [tb09_rare_Z,mul_pow,TailB_rare_sign_square,one_mul]
  have hs' (c : Fin (m+1)) (a b : Bool) :
      (tb09_rare_Z ⟨m,c,a,b⟩)^2=(tb09_rare_h m)^2 := by
    simp only [tb09_rare_Z,mul_pow,TailB_rare_sign_square,one_mul]
  simp_rw [hs']
  simp only [sum_const,card_univ,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul]
  have hp : ((2:ℝ)^(-(m+1:ℤ)))^3=(2:ℝ)^(-3*(m+1:ℤ)) := by
    calc
      _ = ((2:ℝ)^(-(m+1:ℤ)))^(3:ℤ) := by norm_num
      _ = (2:ℝ)^((-(m+1:ℤ))*3) := (_root_.zpow_mul _ _ _).symm
      _ = _ := by congr 1; ring
  rw [← hp]
  dsimp [TailB_rare_p,tb09_rare_h]
  simp only [Nat.cast_add,Nat.cast_one]
  have hm : (m+1:ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem tb09_rare_H_pos : 0 < rareH := by
  rw [← tb09_rare_Z_square]
  have hi : Integrable (fun u => (tb09_rare_Z u)^2) rareLaw :=
    tb09_rare_integrable _ ⟨1,fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (tb09_rare_Z_bound u)⟩
  apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hi).mpr
  let u : RareUnit := ⟨1,0,true,true⟩
  have hu : 0 < (tb09_rare_Z u)^2 := by
    norm_num [u,tb09_rare_Z,tb09_rare_h,rareDelta,signValue]
  calc
    0 < rareLaw {u} := by rw [TailB_rare_atom]; exact ENNReal.ofReal_pos.mpr (TailB_rare_p_pos _)
    _ ≤ _ := measure_mono (by
      intro v hv
      have : v=u := Set.mem_singleton_iff.mp hv
      subst v
      exact ne_of_gt hu)

theorem tb09_rare_Q_pos : 0 < rareQ := by
  have hi : Integrable (fun uv : RareUnit × RareUnit => (rareS uv.1 uv.2)^2)
      (rareLaw.prod rareLaw) :=
    (AronowAudit.Shared.MapTailB.tb09_pair_memLp rareLaw _ (measurable_of_countable _)
      (B := 1) (fun uv => by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [(TailB_rare_s_bounds uv.1 uv.2).1,(TailB_rare_s_bounds uv.1 uv.2).2]) 2).integrable one_le_two
  apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hi).mpr
  have he : Function.support (fun uv : RareUnit × RareUnit => (rareS uv.1 uv.2)^2)=Set.univ := by
    ext uv
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact pow_ne_zero _ (TailB_rare_s_bounds _ _).1.ne'
  rw [he,measure_univ]
  norm_num


theorem tb09_rare_limit_variance_pos : 0 < rareLimitSlopeVariance :=
  div_pos (mul_pos (by norm_num) tb09_rare_H_pos) (sq_pos_of_pos tb09_rare_Q_pos)

def tb09_rare_u (uv : RareUnit × RareUnit) : ℝ := signValue uv.1.B+signValue uv.2.B
def tb09_rare_score (uv : RareUnit × RareUnit) : Vec 2 :=
  ![2*tb09_rare_u uv,2*tb09_rare_u uv+2*tb09_rare_W uv]
def tb09_rare_g (u : RareUnit) : Vec 2 := ![2*signValue u.B,2*signValue u.B+2*tb09_rare_Z u]
def tb09_rare_Γ : Mat 2 := !![4,4;4,4+4*rareH]
def tb09_rare_Qmat : Mat 2 := !![2,2;2,2+2*rareQ]

theorem tb09_rare_u_bound (uv : RareUnit × RareUnit) : |tb09_rare_u uv| ≤ 2 := by
  simpa only [tb09_rare_u,TailB_rare_sign_abs,one_add_one_eq_two] using
    abs_add_le (signValue uv.1.B) (signValue uv.2.B)

theorem tb09_rare_u_row (u : RareUnit) : (∫ v,tb09_rare_u (u,v) ∂rareLaw)=signValue u.B := by
  have hi := tb09_rare_integrable (fun v => signValue v.B) ⟨1,fun v => (TailB_rare_sign_abs _).le⟩
  have hz : (∫ v,signValue v.B ∂rareLaw)=0 := by simpa using tb09_rare_sign_mean false
  change (∫ v,signValue u.B+signValue v.B ∂rareLaw)=_
  rw [integral_add (integrable_const _) hi,integral_const,probReal_univ,one_smul,hz,add_zero]

theorem tb09_rare_score_bound (uv : RareUnit × RareUnit) : ‖tb09_rare_score uv‖ ≤ 8 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 8)).mpr
  intro j
  fin_cases j
  · change |2*tb09_rare_u uv| ≤ 8
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [tb09_rare_u_bound uv]
  · change |2*tb09_rare_u uv+2*tb09_rare_W uv| ≤ 8
    calc
      _ ≤ |2*tb09_rare_u uv|+|2*tb09_rare_W uv| := abs_add_le _ _
      _ ≤ 8 := by rw [abs_mul,abs_mul]; norm_num; linarith [tb09_rare_u_bound uv,tb09_rare_W_bound uv]

theorem tb09_rare_score_symmetric (u v : RareUnit) : tb09_rare_score (u,v)=tb09_rare_score (v,u) := by
  simp only [tb09_rare_score,tb09_rare_W_symmetric u v,tb09_rare_u,add_comm]

theorem tb09_rare_score_projection (u : RareUnit) :
    (fun j => ∫ v,tb09_rare_score (u,v) j ∂rareLaw)=tb09_rare_g u := by
  have hu := tb09_rare_integrable (fun v => tb09_rare_u (u,v)) ⟨2,fun v => tb09_rare_u_bound _⟩
  have hw := tb09_rare_integrable (fun v => tb09_rare_W (u,v)) ⟨2,fun v => tb09_rare_W_bound _⟩
  ext j
  fin_cases j
  · change (∫ v,2*tb09_rare_u (u,v) ∂rareLaw)=2*signValue u.B
    rw [integral_const_mul,tb09_rare_u_row]
  · change (∫ v,2*tb09_rare_u (u,v)+2*tb09_rare_W (u,v) ∂rareLaw)=
      2*signValue u.B+2*tb09_rare_Z u
    rw [integral_add (hu.const_mul 2) (hw.const_mul 2),integral_const_mul,
      integral_const_mul,tb09_rare_u_row,tb09_rare_W_row]
    rfl

theorem tb09_rare_score_mean (j : Fin 2) :
    (∫ uv,tb09_rare_score uv j ∂rareLaw.prod rareLaw)=0 := by
  have hp := AronowAudit.Shared.MapTailB.tb09_pair_memLp rareLaw _
    (measurable_of_countable (fun uv => tb09_rare_score uv j))
    (fun uv => (norm_le_pi_norm (tb09_rare_score uv) j).trans (tb09_rare_score_bound uv)) 2
  rw [integral_prod _ (hp.integrable one_le_two)]
  have he (u : RareUnit) : (∫ v,tb09_rare_score (u,v) j ∂rareLaw)=tb09_rare_g u j :=
    congrFun (tb09_rare_score_projection u) j
  simp_rw [he]
  have hb : (∫ u,signValue u.B ∂rareLaw)=0 := by simpa using tb09_rare_sign_mean false
  fin_cases j
  · change (∫ u,2*signValue u.B ∂rareLaw)=0
    rw [integral_const_mul,hb,mul_zero]
  · change (∫ u,2*signValue u.B+2*tb09_rare_Z u ∂rareLaw)=0
    rw [integral_add ((tb09_rare_integrable _ ⟨1,fun u => (TailB_rare_sign_abs _).le⟩).const_mul 2)
      ((tb09_rare_integrable _ ⟨1,tb09_rare_Z_bound⟩).const_mul 2),
      integral_const_mul,integral_const_mul,hb,tb09_rare_Z_mean]
    ring

theorem tb09_rare_BZ_bound (u : RareUnit) : |signValue u.B*tb09_rare_Z u| ≤ 1 := by
  simpa only [abs_mul,TailB_rare_sign_abs,one_mul] using tb09_rare_Z_bound u

theorem tb09_rare_BZ_mean : (∫ u,signValue u.B*tb09_rare_Z u ∂rareLaw)=0 := by
  rw [tb09_rare_integral _ (tb09_rare_integrable _ ⟨1,tb09_rare_BZ_bound⟩)]
  simp [tb09_rare_Z,Fintype.sum_bool,signValue,← Finset.sum_add_distrib]

theorem tb09_rare_quadratic_integral (a b c : ℝ) :
    (∫ u,a+b*(signValue u.B*tb09_rare_Z u)+c*(tb09_rare_Z u)^2 ∂rareLaw)=a+c*rareH := by
  have hz : Integrable (fun u => (tb09_rare_Z u)^2) rareLaw :=
    tb09_rare_integrable _ ⟨1,fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (tb09_rare_Z_bound u)⟩
  have hb := tb09_rare_integrable _ ⟨1,tb09_rare_BZ_bound⟩
  have hab : Integrable (fun u : RareUnit => a+b*(signValue u.B*tb09_rare_Z u)) rareLaw :=
    (integrable_const a).add (hb.const_mul b)
  rw [integral_add hab (hz.const_mul c),
    integral_add (integrable_const a) (hb.const_mul b),integral_const,
    probReal_univ,one_smul,integral_const_mul,integral_const_mul,
    tb09_rare_BZ_mean,tb09_rare_Z_square,mul_zero,add_zero]

theorem tb09_rare_projection_second :
    (fun j l => ∫ u,tb09_rare_g u j*tb09_rare_g u l ∂rareLaw)=tb09_rare_Γ := by
  ext j l
  fin_cases j <;> fin_cases l
  · change (∫ u,tb09_rare_g u 0*tb09_rare_g u 0 ∂rareLaw)=4
    have he (u : RareUnit) : tb09_rare_g u 0*tb09_rare_g u 0=(4:ℝ) := by
      dsimp [tb09_rare_g]
      nlinarith [TailB_rare_sign_square u.B]
    simp only [he,integral_const,probReal_univ,one_smul,tb09_rare_Γ,Matrix.of_apply,Matrix.cons_val_zero]
  · convert tb09_rare_quadratic_integral 4 4 0 using 1
    · congr 1
      ext u
      dsimp [tb09_rare_g]
      nlinarith [TailB_rare_sign_square u.B]
    · simp [tb09_rare_Γ]
  · convert tb09_rare_quadratic_integral 4 4 0 using 1
    · congr 1
      ext u
      dsimp [tb09_rare_g]
      nlinarith [TailB_rare_sign_square u.B]
    · simp [tb09_rare_Γ]
  · change (∫ u,tb09_rare_g u 1*tb09_rare_g u 1 ∂rareLaw)=4+4*rareH
    convert tb09_rare_quadratic_integral 4 8 4 using 1
    congr 1
    ext u
    dsimp [tb09_rare_g]
    nlinarith [TailB_rare_sign_square u.B]

end AronowAudit.P018.Wave1
