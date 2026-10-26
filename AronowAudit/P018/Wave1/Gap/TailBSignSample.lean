import AronowAudit.P018.Wave1.Gap.TailBSignAlgebra

/-! Exact bread and overlapping meat in the two-sign sample. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def tb05_design {N : ℕ} (z : Fin N → ℝ) (d : Dyad N) : Vec 2 :=
  ![1,1+z (firstUnit d)*z (secondUnit d)]
def tb05_response {N : ℕ} (w : Fin N → ℝ) (d : Dyad N) : ℝ :=
  w (firstUnit d)+w (secondUnit d)
def tb05_T {N : ℕ} (z : Fin N → ℝ) : ℝ :=
  ∑ d : Dyad N,z (firstUnit d)*z (secondUnit d)

theorem tb05_T_formula {N : ℕ} (z : Fin N → ℝ) (hz : ∀ i,(z i)^2=1) :
    tb05_T z = ((∑ i,z i)^2-(N:ℝ))/2 := by
  have h := tb05_pair_product z
  simp only [hz,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  unfold tb05_T
  linarith

theorem tb05_sample_gram {N : ℕ} (z : Fin N → ℝ) (hz : ∀ i,(z i)^2=1) :
    sampleGram (tb05_design z) =
      !![Dreal N,Dreal N+tb05_T z;Dreal N+tb05_T z,2*(Dreal N+tb05_T z)] := by
  have ht (i j : Fin N) : (1+z i*z j)*(1+z i*z j)=2*(1+z i*z j) := by
    have h : (z i*z j)^2=1 := by rw [mul_pow,hz,hz]; ring
    nlinarith [h]
  ext a b
  simp only [sampleGram,Matrix.sum_apply,outer,Matrix.of_apply]
  fin_cases a <;> fin_cases b
  · simp [tb05_design,printed_card_real,printed_dyads_card_real]
  · change (∑ d : Dyad N,1*(1+z (firstUnit d)*z (secondUnit d))) = _
    simp [Finset.sum_add_distrib,printed_card_real,printed_dyads_card_real,tb05_T]
  · change (∑ d : Dyad N,(1+z (firstUnit d)*z (secondUnit d))*1) = _
    simp [Finset.sum_add_distrib,printed_card_real,printed_dyads_card_real,tb05_T]
  · change (∑ d : Dyad N,(1+z (firstUnit d)*z (secondUnit d))*
        (1+z (firstUnit d)*z (secondUnit d))) = 2*(Dreal N+tb05_T z)
    simp_rw [ht]
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    simp [printed_card_real,printed_dyads_card_real,tb05_T]

theorem tb05_sample_inverse {N : ℕ} (z : Fin N → ℝ) (hz : ∀ i,(z i)^2=1)
    (h : (Dreal N)^2-(tb05_T z)^2 ≠ 0) :
    (sampleGram (tb05_design z))⁻¹ =
      ((Dreal N)^2-(tb05_T z)^2)⁻¹ •
        !![2*(Dreal N+tb05_T z),-(Dreal N+tb05_T z);-(Dreal N+tb05_T z),Dreal N] := by
  apply Matrix.inv_eq_left_inv
  rw [tb05_sample_gram z hz]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  all_goals field_simp
  all_goals nlinarith

def tb05_fitA {N : ℕ} (z w : Fin N → ℝ) : ℝ :=
  (Dreal N*((N:ℝ)-1)*(∑ i,w i)-tb05_T z*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i)))/
    ((Dreal N)^2-(tb05_T z)^2)
def tb05_fitB {N : ℕ} (z w : Fin N → ℝ) : ℝ :=
  (Dreal N*((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i))-
    tb05_T z*((N:ℝ)-1)*(∑ i,w i))/((Dreal N)^2-(tb05_T z)^2)

theorem tb05_sample_ols {N : ℕ} (z w : Fin N → ℝ) (hz : ∀ i,(z i)^2=1)
    (h : (Dreal N)^2-(tb05_T z)^2 ≠ 0) :
    sampleOLS (tb05_design z) (tb05_response w) =
      ![tb05_fitA z w-tb05_fitB z w,tb05_fitB z w] := by
  have hm : (∑ d : Dyad N, score (tb05_design z d) (tb05_response w d)) =
      ![((N:ℝ)-1)*(∑ i,w i),((N:ℝ)-1)*(∑ i,w i)+
        ((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i))] := by
    ext a
    simp only [Finset.sum_apply,score,Pi.smul_apply,smul_eq_mul]
    fin_cases a
    · change (∑ d : Dyad N, (w (firstUnit d)+w (secondUnit d))*1) = ((N:ℝ)-1)*(∑ i,w i)
      simpa only [mul_one] using printed_pair_add w
    · change (∑ d : Dyad N, (w (firstUnit d)+w (secondUnit d))*
        (1+z (firstUnit d)*z (secondUnit d))) =
        ((N:ℝ)-1)*(∑ i,w i)+((∑ i,z i)*(∑ i,z i*w i)-(∑ i,w i))
      simp_rw [show ∀ d : Dyad N,(w (firstUnit d)+w (secondUnit d))*
        (1+z (firstUnit d)*z (secondUnit d)) = (w (firstUnit d)+w (secondUnit d))+
        z (firstUnit d)*z (secondUnit d)*(w (firstUnit d)+w (secondUnit d)) from fun d => by ring]
      rw [Finset.sum_add_distrib,printed_pair_add,tb05_pair_mixed z w hz]
  rw [sampleOLS,tb05_sample_inverse z hz h,hm]
  ext a
  fin_cases a <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,tb05_fitA,tb05_fitB,div_eq_mul_inv] <;> ring

theorem tb05_fitted_residual {N : ℕ} (z w : Fin N → ℝ) (hz : ∀ i,(z i)^2=1)
    (h : (Dreal N)^2-(tb05_T z)^2 ≠ 0) (d : Dyad N) :
    fittedResidual (tb05_design z) (tb05_response w) d =
      w (firstUnit d)+w (secondUnit d)-tb05_fitA z w-
        tb05_fitB z w*z (firstUnit d)*z (secondUnit d) := by
  rw [fittedResidual,tb05_sample_ols z w hz h]
  simp [dot,tb05_design,tb05_response,Fin.sum_univ_two]
  ring

/-- Applying a symmetric bread to the overlap identity gives the literal slope entry. -/
theorem tb05_slope_overlap {N : ℕ} (P : Mat 2) (hP : P.IsSymm) (q : Dyad N → Vec 2) :
    sandwich P (meat members q) 1 1 =
      (∑ i : Fin N,(P 1 0*unitScore members q i 0+P 1 1*unitScore members q i 1)^2)-
      ∑ d : Dyad N,(P 1 0*q d 0+P 1 1*q d 1)^2 := by
  have ho (v : Vec 2) : (P*outer v v*P) 1 1 = (P 1 0*v 0+P 1 1*v 1)^2 := by
    simp only [Matrix.mul_apply,Fin.sum_univ_two,outer,Matrix.of_apply]
    rw [← hP.apply 0 1]
    ring
  rw [overlap_meat_identity members members_card (fun d f h => Subtype.ext h) q]
  simp only [sandwich,dyadMeat,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_sum,
    Matrix.sum_mul,Matrix.sub_apply,Matrix.sum_apply,ho]

/-- Exact unnormalized node contribution. -/
def tb05_nodePolynomial (n s u r a b l : ℝ) : ℝ :=
  let A := -l*u+a*(1+l*(n-1))-b*(n-1+l)
  let B := r-a*s+b*l*s
  let C := -2-l*(n-2)
  n*(A^2+B^2+C^2+s^2)+2*((A*B+C*s)*s+(A*C+B*s)*u+(A*s+B*C)*r)
/-- Exact unnormalized subtracted dyad contribution. -/
def tb05_edgePolynomial (n D s u r a b l : ℝ) : ℝ :=
  (1+l^2)*(n*(n-2)+u^2-2*a*(n-1)*u-2*b*(s*r-u)+(a^2+b^2)*D+a*b*(s^2-n))-
  2*l*(s^2+r^2-2*n-2*a*(s*r-u)-2*b*(n-1)*u+(a^2+b^2)*(s^2-n)/2+2*a*b*D)

/-- Exact second-order bread/meat identity. All three sign sums and the OLS fit
are retained; no first-order replacement of the fitted residuals is made. -/
theorem tb05_slope_bread_meat {N : ℕ} (z w : Fin N → ℝ)
    (hz : ∀ i,(z i)^2=1) (hw : ∀ i,(w i)^2=1) (hN : 2 ≤ N)
    (h : (Dreal N)^2-(tb05_T z)^2 ≠ 0) :
    sampleVariance members (tb05_design z) (tb05_response w) 1 1 =
      (tb05_nodePolynomial N (∑ i,z i) (∑ i,w i) (∑ i,z i*w i)
        (tb05_fitA z w) (tb05_fitB z w) (tb05_T z/Dreal N) -
       tb05_edgePolynomial N (Dreal N) (∑ i,z i) (∑ i,w i) (∑ i,z i*w i)
        (tb05_fitA z w) (tb05_fitB z w) (tb05_T z/Dreal N)) /
      ((Dreal N)^2*(1-(tb05_T z/Dreal N)^2)^2) := by
  let D := Dreal N
  let T := tb05_T z
  let a := tb05_fitA z w
  let b := tb05_fitB z w
  let l := T/D
  let H := D*(1-l^2)
  have hD : D ≠ 0 := (printed_Dpos hN).ne'
  have hD' : Dreal N ≠ 0 := hD
  have hHeq : H = (D^2-T^2)/D := by
    dsimp [H,l]
    field_simp [hD]
    <;> ring
  have hH : H ≠ 0 := by
    rw [hHeq]
    exact div_ne_zero h hD
  have hHinv : H⁻¹ = D/(D^2-T^2) := by rw [hHeq,inv_div]
  have hP : ((sampleGram (tb05_design z))⁻¹).IsSymm := by
    rw [tb05_sample_inverse z hz h]
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hinfluence (d : Dyad N) :
      (sampleGram (tb05_design z))⁻¹ 1 0*
        score (tb05_design z d) (fittedResidual (tb05_design z) (tb05_response w) d) 0+
      (sampleGram (tb05_design z))⁻¹ 1 1*
        score (tb05_design z d) (fittedResidual (tb05_design z) (tb05_response w) d) 1 =
      H⁻¹*tb05_slopeScore z w a b l (firstUnit d) (secondUnit d) := by
    rw [tb05_sample_inverse z hz h,tb05_fitted_residual z w hz h,hHinv]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.cons_val_one,Matrix.cons_val_zero,
      Matrix.cons_val_fin_one,score,Pi.smul_apply,tb05_design]
    dsimp [H,l,a,b,D,T,tb05_slopeScore]
    field_simp [hD',h]
    <;> ring
  rw [sampleVariance,tb05_slope_overlap _ hP]
  have hnode (i : Fin N) :
      (sampleGram (tb05_design z))⁻¹ 1 0*unitScore members
          (fun d => score (tb05_design z d) (fittedResidual (tb05_design z) (tb05_response w) d)) i 0+
      (sampleGram (tb05_design z))⁻¹ 1 1*unitScore members
          (fun d => score (tb05_design z d) (fittedResidual (tb05_design z) (tb05_response w) d)) i 1 =
      H⁻¹*((-l*(∑ j,w j)+a*(1+l*((N:ℝ)-1))-b*((N:ℝ)-1+l))+
        ((∑ j,z j*w j)-a*(∑ j,z j)+b*l*(∑ j,z j))*z i+
        (-2-l*((N:ℝ)-2))*w i+(∑ j,z j)*z i*w i) := by
    rw [← tb05_node_score z w hz a b l i,Finset.mul_sum]
    simp only [unitScore,Finset.sum_apply,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hi : i ∈ members d
    · simpa only [hi,if_true] using hinfluence d
    · simp [hi]
  simp_rw [hnode,hinfluence,mul_pow,← Finset.mul_sum]
  rw [tb05_basis_square z w hz hw,tb05_edge_score_square z w hz hw]
  dsimp [tb05_nodePolynomial,tb05_edgePolynomial]
  change H⁻¹^2*_-H⁻¹^2*_ = _
  dsimp [H,l]
  simp only [_root_.mul_inv_rev,inv_pow,mul_pow,div_eq_mul_inv]
  ring

end AronowAudit.P018.Wave1.TailBSign
