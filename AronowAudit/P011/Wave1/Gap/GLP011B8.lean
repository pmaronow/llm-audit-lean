import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_DataMatrixCompletion

namespace AronowAudit.P011.Wave1
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology Classical ENNReal ProbabilityTheory
noncomputable section
attribute [-simp] Finset.sum_boole
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-- Normalized finite-source expectation. -/
def rmr_E {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ u, f u) / (Fintype.card (Fin n → Bool) : ℝ)

def rmr_w (m : ℕ) (i : Fin (4*m)) : ℝ :=
  (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
def rmr_a (m : ℕ) (i : Fin (4*m)) : ℝ :=
  (![1,0,1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
def rmr_c (m : ℕ) (i : Fin (4*m)) : ℝ :=
  if i.val%2=0 then 1 else (4*m : ℝ)
def rmr_Y (m : ℕ) (u : Fin (4*m) → Bool) : Fin (4*m) → ℝ :=
  fun i => rmr_c m i * sign (u i)
def rmr_D (m : ℕ) : Matrix (Fin (4*m)) (Fin 2) ℝ :=
  fun i j => if j=0 then 1 else rmr_w m i

def rmr_L {n : ℕ} (v : Fin n → ℝ) (u : Fin n → Bool) : ℝ :=
  ∑ i, v i * sign (u i)
def rmr_A (m : ℕ) := rmr_L (rmr_a m)
def rmr_B (m : ℕ) := rmr_L (fun i => 1-rmr_a m i)
def rmr_C (m : ℕ) := rmr_L (rmr_w m)

lemma rmr_E_const {n : ℕ} (c : ℝ) : rmr_E (n:=n) (fun _ => c) = c := by
  classical
  simp [rmr_E]
lemma rmr_E_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    rmr_E (fun u => f u+g u) = rmr_E f+rmr_E g := by
  simp only [rmr_E, Finset.sum_add_distrib, add_div]
lemma rmr_E_sub {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    rmr_E (fun u => f u-g u) = rmr_E f-rmr_E g := by
  simp only [rmr_E, Finset.sum_sub_distrib, sub_div]
lemma rmr_E_mul {n : ℕ} (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    rmr_E (fun u => c*f u) = c*rmr_E f := by
  simp only [rmr_E, ←Finset.mul_sum]; ring
lemma rmr_E_div {n : ℕ} (f : (Fin n → Bool) → ℝ) (c : ℝ) :
    rmr_E (fun u => f u/c) = rmr_E f/c := by
  simp only [rmr_E, ←Finset.sum_div]; ring
lemma rmr_E_sum {n : ℕ} {I : Type} [Fintype I]
    (f : I → (Fin n → Bool) → ℝ) :
    rmr_E (fun u => ∑ i, f i u) = ∑ i, rmr_E (f i) := by
  simp only [rmr_E, ←Finset.sum_div]; rw [Finset.sum_comm]

lemma rmr_E_sign {n : ℕ} (i : Fin n) :
    rmr_E (fun u => sign (u i)) = 0 := by
  rw [rmr_E, BlockOLSCompletion.uniform_coordinate_sum]
  norm_num [Fintype.sum_bool, sign]

lemma rmr_E_sign_mul {n : ℕ} (i j : Fin n) :
    rmr_E (fun u => sign (u i)*sign (u j)) = if i=j then 1 else 0 := by
  have hc := DataMatrixCompletion.covariance_formula i j
  have hz (i : Fin n) : expectation (signModel n) (fun y => y i) = 0 := by
    rw [DataMatrixCompletion.coord_integral i (fun x => x) measurable_id]
    norm_num
  have he : covariance (signModel n) i j = rmr_E (fun u => sign (u i)*sign (u j)) := by
    unfold covariance
    simp only [weighted, signModel, one_mul]
    change (∫ y, (y i-expectation (signModel n) (fun z => z i))*
      (y j-expectation (signModel n) (fun z => z j)) ∂(signModel n).law) = _
    rw [hz i, hz j]
    simp only [sub_zero]
    exact uniform_integral _ (measurable_of_finite _) _ (by fun_prop)
  rw [he] at hc
  exact hc

lemma rmr_E_L {n : ℕ} (v : Fin n → ℝ) : rmr_E (rmr_L v) = 0 := by
  unfold rmr_L
  rw [rmr_E_sum]
  simp only [rmr_E_mul, rmr_E_sign, mul_zero, Finset.sum_const_zero]
lemma rmr_E_LL {n : ℕ} (v z : Fin n → ℝ) :
    rmr_E (fun u => rmr_L v u*rmr_L z u) = ∑ i, v i*z i := by
  simp only [rmr_L, Finset.sum_mul_sum]
  rw [rmr_E_sum]
  simp_rw [rmr_E_sum]
  have he (i j : Fin n) :
      rmr_E (fun u => v i*sign (u i)*(z j*sign (u j))) =
        v i*z j*(if i=j then 1 else 0) := by
    simp_rw [show ∀ u : Fin n → Bool, v i*sign (u i)*(z j*sign (u j)) =
      (v i*z j)*(sign (u i)*sign (u j)) by intro u; ring]
    rw [rmr_E_mul, rmr_E_sign_mul]
  simp_rw [he]
  simp
lemma rmr_E_L_sq {n : ℕ} (v : Fin n → ℝ) :
    rmr_E (fun u => rmr_L v u^2) = ∑ i, v i^2 := by
  simpa only [pow_two] using rmr_E_LL v v

lemma rmr_local_sum (m : ℕ) (f : Fin 4 → ℝ) :
    (∑ i : Fin (4*m), f (localIndex (by decide) i)) = (m:ℝ)*∑ r, f r :=
  BlockOLSCompletion.local_sum (by decide) f

lemma rmr_point (m : ℕ) (i : Fin (4*m)) :
    rmr_a m i^2=rmr_a m i ∧ rmr_w m i^2=rmr_a m i ∧
    rmr_w m i*rmr_a m i=rmr_w m i ∧
    rmr_c m i=rmr_a m i+(4*m:ℝ)*(1-rmr_a m i) ∧
    rmr_w m i*rmr_c m i=rmr_w m i ∧
    0 ≤ rmr_a m i ∧ rmr_a m i ≤ 1 ∧ |rmr_w m i| ≤ 1 := by
  have hh : i.val%2 = (localIndex (q:=4) (by decide) i).val%2 := by
    dsimp [localIndex]; omega
  unfold rmr_a rmr_w rmr_c
  generalize hr : localIndex (q:=4) (by decide) i = r at *
  fin_cases r <;> norm_num at hh ⊢ <;> simp [hh]

lemma rmr_sums (m : ℕ) :
    (∑ i, rmr_a m i) = 2*(m:ℝ) ∧ (∑ i, rmr_w m i) = 0 ∧
    (∑ i, rmr_w m i^2) = 2*(m:ℝ) ∧ (∑ i, (1-rmr_a m i)^2) = 2*(m:ℝ) ∧
    (∑ i, rmr_a m i*(1-rmr_a m i)) = 0 := by
  have ha : (∑ i, rmr_a m i) = 2*(m:ℝ) := by
    unfold rmr_a; rw [rmr_local_sum]; norm_num [Fin.sum_univ_succ]; ring
  have hw : (∑ i, rmr_w m i) = 0 := by
    unfold rmr_w; rw [rmr_local_sum]; norm_num [Fin.sum_univ_succ]
  refine ⟨ha, hw, ?_, ?_, ?_⟩
  · simpa only [(rmr_point m _).2.1] using ha
  · calc
      (∑ i, (1-rmr_a m i)^2) = ∑ i, (1-rmr_a m i) := by
        apply Finset.sum_congr rfl; intro i _
        nlinarith [(rmr_point m i).1]
      _ = 2*(m:ℝ) := by rw [Finset.sum_sub_distrib, ha]; simp; push_cast; ring
  · have h (i : Fin (4*m)) : rmr_a m i*(1-rmr_a m i)=0 := by
      nlinarith [(rmr_point m i).1]
    simp [h]

lemma rmr_moments (m : ℕ) :
    rmr_E (rmr_A m)=0 ∧ rmr_E (rmr_B m)=0 ∧ rmr_E (rmr_C m)=0 ∧
    rmr_E (fun u => rmr_A m u^2)=2*(m:ℝ) ∧
    rmr_E (fun u => rmr_B m u^2)=2*(m:ℝ) ∧
    rmr_E (fun u => rmr_C m u^2)=2*(m:ℝ) ∧
    rmr_E (fun u => rmr_A m u*rmr_B m u)=0 := by
  have ha : (∑ i, rmr_a m i^2)=2*(m:ℝ) := by
    simp_rw [(rmr_point m _).1]; exact (rmr_sums m).1
  exact ⟨rmr_E_L _, rmr_E_L _, rmr_E_L _,
    (rmr_E_L_sq _).trans ha,
    (rmr_E_L_sq _).trans (rmr_sums m).2.2.2.1,
    (rmr_E_L_sq _).trans (rmr_sums m).2.2.1,
    (rmr_E_LL _ _).trans (rmr_sums m).2.2.2.2⟩

lemma rmr_expectation (m : ℕ) (f : (Fin (4*m) → ℝ) → ℝ) (hf : Measurable f) :
    expectation (unstableModel m) f = rmr_E (fun u => f (rmr_Y m u)) :=
  uniform_integral _ (measurable_of_finite _) f hf

lemma rmr_gram (m : ℕ) : (rmr_D m)ᵀ*rmr_D m =
    Matrix.diagonal (![(4*m:ℝ), 2*(m:ℝ)]) := by
  have hw := (rmr_sums m).2.1
  have hw2 := (rmr_sums m).2.2.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rmr_D, Matrix.diagonal_apply, hw, ←pow_two, hw2]

lemma rmr_ols (m : ℕ) (hm : 0<m) (y : Fin (4*m) → ℝ) :
    ols (rmr_D m) y = ![(∑ i, y i)/(4*m:ℝ),
      (∑ i, rmr_w m i*y i)/(2*m:ℝ)] := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hi : ((rmr_D m)ᵀ*rmr_D m)⁻¹ =
      Matrix.diagonal (![(4*m:ℝ)⁻¹, (2*m:ℝ)⁻¹]) := by
    apply Matrix.inv_eq_left_inv
    rw [rmr_gram]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply, hm0] <;>
        field_simp
  unfold ols
  rw [hi]
  ext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply,
      rmr_D, div_eq_mul_inv, mul_comm]

lemma rmr_source_sums (m : ℕ) (u : Fin (4*m) → Bool) :
    (∑ i, rmr_Y m u i) = rmr_A m u+(4*m:ℝ)*rmr_B m u ∧
    (∑ i, rmr_w m i*rmr_Y m u i) = rmr_C m u := by
  constructor
  · unfold rmr_Y rmr_A rmr_B rmr_L
    simp_rw [(rmr_point m _).2.2.2.1, add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · unfold rmr_Y rmr_C rmr_L
    apply Finset.sum_congr rfl
    intro i _
    rw [←mul_assoc, (rmr_point m i).2.2.2.2.1]

lemma rmr_ols_source (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    ols (rmr_D m) (rmr_Y m u) =
      ![rmr_A m u/(4*m:ℝ)+rmr_B m u, 2*rmr_C m u/(4*m:ℝ)] := by
  rw [rmr_ols m hm, (rmr_source_sums m u).1, (rmr_source_sums m u).2]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  ext j
  fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · field_simp <;> ring
  · field_simp <;> ring

lemma rmr_betaHat_source (m : ℕ) (u : Fin (4*m) → Bool) :
    betaHat (unstableModel m) (rmr_Y m u) = 2*rmr_C m u/(4*m:ℝ) := by
  simp only [betaHat, average, weighted, unstableModel, Nat.cast_mul, Nat.cast_ofNat]
  change (∑ i, 2*rmr_w m i*rmr_Y m u i)/(4*m:ℝ) = _
  rw [show (∑ i, 2*rmr_w m i*rmr_Y m u i) =
      2*∑ i, rmr_w m i*rmr_Y m u i by simp only [Finset.mul_sum, mul_assoc],
    (rmr_source_sums m u).2]

lemma rmr_beta (m : ℕ) : beta (unstableModel m)=0 := by
  unfold beta
  rw [rmr_expectation _ _ (by unfold betaHat average weighted; fun_prop)]
  simp_rw [rmr_betaHat_source]
  rw [rmr_E_div, rmr_E_mul, (rmr_moments m).2.2.1]
  ring

lemma rmr_scaled_variance (m : ℕ) (hm : 0<m) :
    (4*m:ℝ)*var (unstableModel m) (betaHat (unstableModel m))=2 := by
  unfold var
  change (4*m:ℝ)*expectation (unstableModel m)
    (fun y => (betaHat (unstableModel m) y-beta (unstableModel m))^2)=2
  rw [rmr_beta, rmr_expectation _ _ (by unfold betaHat average weighted; fun_prop)]
  simp only [sub_zero, rmr_betaHat_source]
  have he (u : Fin (4*m) → Bool) : (2*rmr_C m u/(4*m:ℝ))^2 =
      (4/(4*m:ℝ)^2)*rmr_C m u^2 := by ring
  simp_rw [he]
  rw [rmr_E_mul, (rmr_moments m).2.2.2.2.2.1]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

lemma rmr_intercept_moments (m : ℕ) (hm : 0<m) :
    expectation (unstableModel m) (fun y => ols (rmr_D m) y 0)=0 ∧
    var (unstableModel m) (fun y => ols (rmr_D m) y 0) =
      (4*m:ℝ)/2+1/(2*(4*m:ℝ)) := by
  have hmeas : Measurable (fun y => ols (rmr_D m) y 0) := by
    simp only [rmr_ols m hm, Matrix.cons_val_zero]
    fun_prop
  have he : expectation (unstableModel m) (fun y => ols (rmr_D m) y 0)=0 := by
    rw [rmr_expectation _ _ hmeas]
    simp_rw [rmr_ols_source m hm, Matrix.cons_val_zero]
    rw [rmr_E_add, rmr_E_div, (rmr_moments m).1, (rmr_moments m).2.1]
    ring
  refine ⟨he, ?_⟩
  unfold var
  rw [he]
  simp only [sub_zero]
  rw [rmr_expectation _ _ (by fun_prop)]
  simp only [sub_zero, rmr_ols_source m hm, Matrix.cons_val_zero]
  have hex (u : Fin (4*m) → Bool) :
      (rmr_A m u/(4*m:ℝ)+rmr_B m u)^2 =
        rmr_A m u^2/(4*m:ℝ)^2+rmr_B m u^2+
        (2/(4*m:ℝ))*(rmr_A m u*rmr_B m u) := by ring
  simp_rw [hex]
  rw [rmr_E_add, rmr_E_add, rmr_E_div, rmr_E_mul,
    (rmr_moments m).2.2.2.1, (rmr_moments m).2.2.2.2.1,
    (rmr_moments m).2.2.2.2.2.2]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

def rmr_T (m : ℕ) (y : Fin (4*m) → ℝ) : ℝ :=
  (4*m:ℝ)*VResidual (unstableModel m).G
    (fittedResidual (unstableModel m) (rmr_D m) (ols (rmr_D m)) y)

lemma rmr_sign_sq (b : Bool) : sign b^2=1 := by cases b <;> norm_num [sign]
lemma rmr_sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

lemma rmr_square_sum (m : ℕ) (u : Fin (4*m) → Bool) (a b : ℝ) :
    (∑ i, rmr_a m i*(sign (u i)-a-rmr_w m i*b)^2) =
      2*m+2*m*a^2+2*m*b^2-2*a*rmr_A m u-2*b*rmr_C m u := by
  have he (i : Fin (4*m)) :
      rmr_a m i*(sign (u i)-a-rmr_w m i*b)^2 =
      rmr_a m i+a^2*rmr_a m i+b^2*rmr_a m i-
        2*a*(rmr_a m i*sign (u i))-2*b*(rmr_w m i*sign (u i))+
        2*a*b*rmr_w m i := by
    have haw : rmr_a m i*rmr_w m i=rmr_w m i := by
      rw [mul_comm, (rmr_point m i).2.2.1]
    calc
      _ = rmr_a m i*sign (u i)^2+a^2*rmr_a m i+
        b^2*(rmr_a m i*rmr_w m i^2)-2*a*(rmr_a m i*sign (u i))-
        2*b*((rmr_a m i*rmr_w m i)*sign (u i))+2*a*b*(rmr_a m i*rmr_w m i) := by ring
      _ = _ := by rw [rmr_sign_sq, (rmr_point m i).2.1,
        ←pow_two, (rmr_point m i).1, haw]; ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ←Finset.mul_sum]
  change (∑ i, rmr_a m i)+a^2*(∑ i, rmr_a m i)+b^2*(∑ i, rmr_a m i)-
    2*a*rmr_A m u-2*b*rmr_C m u+2*a*b*(∑ i, rmr_w m i)=_
  rw [(rmr_sums m).1, (rmr_sums m).2.1]
  ring

lemma rmr_T_sum (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    rmr_T m (rmr_Y m u) = (4/(4*m:ℝ))*
      ∑ i, rmr_a m i*(sign (u i)-(rmr_A m u/(4*m:ℝ)+rmr_B m u)-
        rmr_w m i*(2*rmr_C m u/(4*m:ℝ)))^2 := by
  have hq (x : Fin (4*m) → ℝ) : quadratic (oracleMatrix (emptyGraph (4*m))) x =
      ∑ i, x i^2 := by
    simp [quadratic, oracleMatrix, adjacency, emptyGraph, Matrix.one_apply, pow_two]
  unfold rmr_T VResidual
  rw [show (unstableModel m).G=emptyGraph (4*m) from rfl, hq]
  have hr (i : Fin (4*m)) :
      fittedResidual (unstableModel m) (rmr_D m) (ols (rmr_D m)) (rmr_Y m u) i =
        2*rmr_w m i*(sign (u i)-(rmr_A m u/(4*m:ℝ)+rmr_B m u)-
          rmr_w m i*(2*rmr_C m u/(4*m:ℝ))) := by
    unfold fittedResidual
    rw [rmr_ols_source m hm]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [rmr_D, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, ite_true, one_mul, Fin.reduceEq, ite_false]
    change 2*rmr_w m i*(rmr_c m i*sign (u i)-_) = _
    have hc := (rmr_point m i).2.2.2.2.1
    calc
      _ = 2*(rmr_w m i*rmr_c m i)*sign (u i)-
        2*rmr_w m i*(rmr_A m u/(4*m:ℝ)+rmr_B m u)-
        2*rmr_w m i^2*(2*rmr_C m u/(4*m:ℝ)) := by ring
      _ = _ := by rw [hc]; ring
  simp_rw [hr, show ∀ (w x : ℝ), (2*w*x)^2=4*w^2*x^2 by intros; ring,
    (rmr_point m _).2.1]
  simp only [mul_assoc]
  rw [←Finset.mul_sum]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  generalize (∑ i, rmr_a m i*(sign (u i)-(rmr_A m u/(4*m:ℝ)+rmr_B m u)-
    rmr_w m i*(2*rmr_C m u/(4*m:ℝ)))^2) = S
  field_simp <;> ring

lemma rmr_T_expansion (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    rmr_T m (rmr_Y m u) = 2+2*rmr_B m u^2-
      (4/(4*m:ℝ))*(rmr_A m u*rmr_B m u)-
      (6/(4*m:ℝ)^2)*rmr_A m u^2-(8/(4*m:ℝ)^2)*rmr_C m u^2 := by
  rw [rmr_T_sum m hm, rmr_square_sum]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

lemma rmr_T_measurable (m : ℕ) : Measurable (rmr_T m) := by
  unfold rmr_T VResidual quadratic fittedResidual Matrix.mulVec dotProduct
  unfold ols Matrix.mulVec dotProduct
  fun_prop

lemma rmr_T_expectation (m : ℕ) (hm : 0<m) :
    expectation (unstableModel m) (rmr_T m) = (4*m:ℝ)+2-7/(4*m:ℝ) := by
  rw [rmr_expectation _ _ (rmr_T_measurable m)]
  simp_rw [rmr_T_expansion m hm]
  rw [rmr_E_sub, rmr_E_sub, rmr_E_sub, rmr_E_add, rmr_E_const,
    rmr_E_mul, rmr_E_mul, rmr_E_mul, rmr_E_mul,
    (rmr_moments m).2.2.2.1, (rmr_moments m).2.2.2.2.1,
    (rmr_moments m).2.2.2.2.2.1, (rmr_moments m).2.2.2.2.2.2]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

lemma rmr_mean_model (m : ℕ) : MeanModel (unstableModel m) (rmr_D m) 0 := by
  let : IsProbabilityMeasure (uniformLaw (rmr_Y m)) := by
    change IsProbabilityMeasure (unstableModel m).law
    exact (unstableModel m).probability
  constructor
  · intro i
    exact (NewFiniteCompletion.finite_memLp (rmr_Y m) _ (measurable_pi_apply i) 2).integrable
      (by norm_num)
  · intro i
    rw [rmr_expectation _ _ (measurable_pi_apply i)]
    change rmr_E (fun u => rmr_c m i*sign (u i)) = _
    rw [rmr_E_mul, rmr_E_sign]
    simp

lemma rmr_ae_source (m : ℕ) {p : (Fin (4*m) → ℝ) → Prop}
    (hp : ∀ u, p (rmr_Y m u)) : ∀ᵐ y ∂(unstableModel m).law, p y := by
  have hm : (unstableModel m).law =
      (PMF.uniformOfFintype (Fin (4*m) → Bool)).toMeasure.map (rmr_Y m) :=
    (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm
  have hs : ∀ᵐ y ∂(unstableModel m).law, y ∈ Set.range (rmr_Y m) := by
    rw [hm]
    apply (ae_map_iff (measurable_of_finite _).aemeasurable
      (Set.finite_range (rmr_Y m)).measurableSet).mpr
    exact Filter.Eventually.of_forall (fun u => ⟨u,rfl⟩)
  filter_upwards [hs] with y hy
  rcases hy with ⟨u,rfl⟩
  exact hp u

lemma rmr_weighted_source (m : ℕ) (u : Fin (4*m) → Bool) (i : Fin (4*m)) :
    weighted (unstableModel m) (rmr_Y m u) i = 2*rmr_w m i*sign (u i) := by
  change 2*rmr_w m i*(rmr_c m i*sign (u i)) = _
  rw [←mul_assoc, mul_assoc 2, (rmr_point m i).2.2.2.2.1]

lemma rmr_scaling : Scaling unstableFamily 2 1 2 3 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro a b hab
      change 4*(a+1) ≤ 4*(b+1)
      omega
    · intro k
      let e : Fin (4*(k+1)) ↪ Fin (4*(k+1+1)) :=
        ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩,
          by intro i j h; exact Fin.ext (congrArg (fun x : Fin (4*(k+1+1)) => x.val) h)⟩
      exact ⟨e, fun _ _ => rfl⟩
  · intro k
    exact uniform_coordinate_dependency Bool (fun i b => rmr_c (k+1) i*sign b)
      (fun _ => measurable_of_finite _)
  · intro k
    change ∀ᵐ y ∂(unstableModel (k+1)).law, ∀ i,
      |weighted (unstableModel (k+1)) y i-beta (unstableModel (k+1))|≤2
    rw [rmr_beta]
    apply rmr_ae_source
    intro u i
    rw [rmr_weighted_source]
    simp only [sub_zero, abs_mul, Nat.abs_ofNat, rmr_sign_abs, mul_one]
    nlinarith [(rmr_point (k+1) i).2.2.2.2.2.2.2]
  · intro k i
    simp [degree, unstableFamily, unstableModel, emptyGraph]
  · have he : (fun k => (unstableFamily.size k:ℝ)*var (unstableFamily.model k)
        (betaHat (unstableFamily.model k))) = fun _ => (2:ℝ) := by
      funext k
      simpa only [unstableFamily, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        rmr_scaled_variance (k+1) (Nat.succ_pos k)
    rw [he]
    exact tendsto_const_nhds
  · intro k i
    change |2*rmr_w (k+1) i|<3
    rw [abs_mul]
    norm_num only [Nat.abs_ofNat]
    nlinarith [(rmr_point (k+1) i).2.2.2.2.2.2.2]

/-- Orthogonal decomposition on the observations with nonzero slope weight. -/
lemma rmr_T_square_decomposition (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    rmr_T m (rmr_Y m u) = (4/(4*m:ℝ))*
      (∑ i, rmr_a m i*(sign (u i)-2*rmr_A m u/(4*m:ℝ)-
        rmr_w m i*(2*rmr_C m u/(4*m:ℝ)))^2)+
      2*(rmr_B m u-rmr_A m u/(4*m:ℝ))^2 := by
  rw [rmr_T_expansion m hm, rmr_square_sum]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

lemma rmr_T_lower (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    2*(rmr_B m u-rmr_A m u/(4*m:ℝ))^2 ≤ rmr_T m (rmr_Y m u) := by
  rw [rmr_T_square_decomposition m hm]
  have hs : 0 ≤ ∑ i, rmr_a m i*(sign (u i)-2*rmr_A m u/(4*m:ℝ)-
        rmr_w m i*(2*rmr_C m u/(4*m:ℝ)))^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (rmr_point m i).2.2.2.2.2.1 (sq_nonneg _))
  have hc : 0 ≤ 4/(4*m:ℝ) := by positivity
  nlinarith [mul_nonneg hc hs]

lemma rmr_A_bound (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    |rmr_A m u/(4*m:ℝ)| ≤ 1/2 := by
  have hb : |rmr_A m u| ≤ 2*m := by
    calc
      _ ≤ ∑ i, |rmr_a m i*sign (u i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, rmr_a m i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, rmr_sign_abs, mul_one,
          abs_of_nonneg (rmr_point m i).2.2.2.2.2.1]
      _ = _ := (rmr_sums m).1
  rw [abs_div, abs_of_pos (by positivity : 0<(4*m:ℝ))]
  apply (div_le_iff₀ (by positivity : 0<(4*m:ℝ))).mpr
  nlinarith

lemma rmr_B_even (m : ℕ) (u : Fin (4*m) → Bool) :
    ∃ z : ℤ, rmr_B m u=2*(z:ℝ) := by
  have he : rmr_B m u = ∑ b : Fin m,
      (sign (u (StarCompletion.blockEquiv 4 m (b,1)))+
        sign (u (StarCompletion.blockEquiv 4 m (b,3)))) := by
    unfold rmr_B rmr_L
    rw [←(StarCompletion.blockEquiv 4 m).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    simp [rmr_a, StarCompletion.block_local, Fin.sum_univ_succ]
  have hp (b : Fin m) : ∃ z : ℤ,
      sign (u (StarCompletion.blockEquiv 4 m (b,1)))+
        sign (u (StarCompletion.blockEquiv 4 m (b,3)))=2*(z:ℝ) := by
    cases h1 : u (StarCompletion.blockEquiv 4 m (b,1)) <;>
      cases h3 : u (StarCompletion.blockEquiv 4 m (b,3))
    · exact ⟨-1, by norm_num [sign]⟩
    · exact ⟨0, by norm_num [sign]⟩
    · exact ⟨0, by norm_num [sign]⟩
    · exact ⟨1, by norm_num [sign]⟩
  choose z hz using hp
  refine ⟨∑ b, z b, ?_⟩
  rw [he]
  simp_rw [hz]
  simp [←Finset.mul_sum]

lemma rmr_failure (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool)
    (hu : rmr_B m u ≠ 0) : 1 < |rmr_T m (rmr_Y m u)-2| := by
  obtain ⟨z,hz⟩ := rmr_B_even m u
  have hz0 : z≠0 := by intro h; simp [h] at hz; exact hu hz
  have hB : 2 ≤ |rmr_B m u| := by
    have hcases : z ≤ -1 ∨ 1 ≤ z := by omega
    rcases hcases with h | h
    · have hr : (z:ℝ) ≤ -1 := by exact_mod_cast h
      rw [hz]
      have hab : -(2*(z:ℝ)) ≤ |2*(z:ℝ)| := neg_le_abs _
      linarith
    · have hr : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast h
      rw [hz]
      have hab : 2*(z:ℝ) ≤ |2*(z:ℝ)| := le_abs_self _
      linarith
  have hA := rmr_A_bound m hm u
  have hdiff := abs_sub_abs_le_abs_sub (rmr_B m u) (rmr_A m u/(4*m:ℝ))
  have hlow := rmr_T_lower m hm u
  have hsq := sq_nonneg (|rmr_B m u-rmr_A m u/(4*m:ℝ)|-3/2)
  have hab := le_abs_self (rmr_T m (rmr_Y m u)-2)
  nlinarith [sq_abs (rmr_B m u-rmr_A m u/(4*m:ℝ))]

/-- Flip one source sign; uniform finite-source expectation is invariant. -/
def rmr_flip {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun u := Function.update u i (!(u i))
  invFun u := Function.update u i (!(u i))
  left_inv u := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  right_inv u := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj]

lemma rmr_E_equiv {n : ℕ} (e : (Fin n → Bool) ≃ (Fin n → Bool))
    (f : (Fin n → Bool) → ℝ) : rmr_E (fun u => f (e u))=rmr_E f := by
  unfold rmr_E
  rw [e.sum_comp]

lemma rmr_L_update {n : ℕ} (v : Fin n → ℝ) (u : Fin n → Bool) (i : Fin n) (b : Bool) :
    rmr_L v (Function.update u i b) = rmr_L v u+v i*(sign b-sign (u i)) := by
  unfold rmr_L
  have he : (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      v j*sign (Function.update u i b j)) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, v j*sign (u j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i), he,
    ←Finset.sum_erase_add _ (fun j => v j*sign (u j)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  ring

lemma rmr_sign_flip (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

lemma rmr_B_flip (m : ℕ) (hm : 0<m) (u : Fin (4*m) → Bool) :
    rmr_B m (rmr_flip (⟨1,by omega⟩ : Fin (4*m)) u) =
      rmr_B m u-2*sign (u ⟨1,by omega⟩) := by
  change rmr_L _ (Function.update u _ _) = _
  rw [rmr_L_update, rmr_sign_flip]
  have ha : rmr_a m (⟨1,by omega⟩ : Fin (4*m))=0 := by
    norm_num [rmr_a, localIndex]
  rw [ha]
  unfold rmr_B
  ring

lemma rmr_B_failure_mass (m : ℕ) (hm : 0<m) :
    (1/2:ℝ) ≤ rmr_E (fun u => if rmr_B m u≠0 then 1 else 0) := by
  let i : Fin (4*m) := ⟨1,by omega⟩
  let f : (Fin (4*m) → Bool) → ℝ := fun u => if rmr_B m u≠0 then 1 else 0
  have hpair (u : Fin (4*m) → Bool) : 1 ≤ f u+f (rmr_flip i u) := by
    have hor : rmr_B m u≠0 ∨ rmr_B m (rmr_flip i u)≠0 := by
      by_cases h : rmr_B m u=0
      · right
        rw [rmr_B_flip m hm, h]
        cases hsign : u i <;> norm_num [i,sign] at *
      · exact Or.inl h
    rcases hor with h | h <;> simp [f,h] <;> split_ifs <;> norm_num
  have hsum : rmr_E (fun _ : Fin (4*m) → Bool => (1:ℝ)) ≤
      rmr_E (fun u => f u+f (rmr_flip i u)) := by
    unfold rmr_E
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hpair u)) (by positivity)
  rw [rmr_E_const, rmr_E_add, rmr_E_equiv] at hsum
  dsimp [f] at hsum
  linarith

lemma rmr_failure_probability (m : ℕ) (hm : 0<m) :
    (1/2:ℝ) ≤ probability (unstableModel m) {y | |rmr_T m y-2| > 1} := by
  have hset : MeasurableSet {y : Fin (4*m) → ℝ | |rmr_T m y-2| > 1} :=
    measurableSet_lt measurable_const (by
      have := rmr_T_measurable m
      fun_prop)
  have he : probability (unstableModel m) {y | |rmr_T m y-2| > 1} =
      rmr_E (fun u => if 1 < |rmr_T m (rmr_Y m u)-2| then 1 else 0) := by
    unfold probability
    rw [←integral_indicator_one hset]
    change expectation (unstableModel m) _ = _
    change expectation (unstableModel m)
      (fun y => if 1 < |rmr_T m y-2| then (1:ℝ) else 0) = _
    exact rmr_expectation _ _ (Measurable.ite hset measurable_const measurable_const)
  apply (rmr_B_failure_mass m hm).trans
  rw [he]
  unfold rmr_E
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro u _
  by_cases h : rmr_B m u≠0
  · simp [h, rmr_failure m hm u h]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem residual_missing_regularity_proof :
    Scaling unstableFamily 2 1 2 3 ∧
    (∀ k, let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
      if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
      MeanModel (unstableFamily.model k) D 0 ∧
      var (unstableFamily.model k) (fun y => ols D y 0) =
        (unstableFamily.size k : ℝ)/2+1/(2*(unstableFamily.size k : ℝ)) ∧
      expectation (unstableFamily.model k) (fun y => (unstableFamily.size k : ℝ)*
        VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) =
        (unstableFamily.size k : ℝ)+2-7/(unstableFamily.size k : ℝ)) ∧
    ¬ InProbability unstableFamily
      (fun k y => let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
        if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
        (unstableFamily.size k : ℝ)*VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) (fun _ => 2)  := by
  refine ⟨rmr_scaling, ?_, ?_⟩
  · intro k
    change MeanModel (unstableModel (k+1)) (rmr_D (k+1)) 0 ∧
      var (unstableModel (k+1)) (fun y => ols (rmr_D (k+1)) y 0) =
        ((4*(k+1):ℕ):ℝ)/2+1/(2*((4*(k+1):ℕ):ℝ)) ∧
      expectation (unstableModel (k+1)) (fun y => ((4*(k+1):ℕ):ℝ)*
        VResidual (unstableModel (k+1)).G
          (fittedResidual (unstableModel (k+1)) (rmr_D (k+1)) (ols (rmr_D (k+1))) y)) =
        ((4*(k+1):ℕ):ℝ)+2-7/((4*(k+1):ℕ):ℝ)
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact ⟨rmr_mean_model _, (rmr_intercept_moments (k+1) (Nat.succ_pos k)).2,
      rmr_T_expectation (k+1) (Nat.succ_pos k)⟩
  · intro h
    have ht := h 1 (by norm_num)
    change Tendsto (fun k => probability (unstableModel (k+1))
      {y | |((4*(k+1):ℕ):ℝ)*VResidual (unstableModel (k+1)).G
        (fittedResidual (unstableModel (k+1)) (rmr_D (k+1)) (ols (rmr_D (k+1))) y)-2| > 1})
      atTop (𝓝 0) at ht
    simp only [Nat.cast_mul, Nat.cast_ofNat] at ht
    have hl : (1/2:ℝ) ≤ 0 := ge_of_tendsto' ht (fun k =>
      rmr_failure_probability (k+1) (Nat.succ_pos k))
    norm_num at hl

end
end AronowAudit.P011.Wave1
