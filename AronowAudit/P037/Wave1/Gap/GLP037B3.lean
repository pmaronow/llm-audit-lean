import AronowAudit.P037.P037_Regression
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A normal-equation certificate identifies the actual inverse-form WLS fit. -/
lemma collapsedControls_fit_of_normal {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (Y : I → ℝ) (b : K → ℝ)
    (hw : ∀ i, 0 < w i) (hX : Function.Injective X.mulVec)
    (hn : ∀ k, (∑ i, w i * (Y i - X.mulVec b i) * X i k) = 0) :
    (regressionMap w X).mulVec Y = b := by
  classical
  have hzero : (X.transpose * Matrix.diagonal w).mulVec (Y-X.mulVec b) = 0 := by
    ext k
    rw [← Matrix.mulVec_mulVec]
    change (∑ i, X i k * (Matrix.diagonal w).mulVec (Y-X.mulVec b) i) = 0
    simp only [Matrix.mulVec_diagonal, Pi.sub_apply]
    convert hn k using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he := congrArg
    ((X.transpose * Matrix.diagonal w * X)⁻¹).mulVec hzero
  have hleft := RegressionCompletion.weighted_left_inverse w X hw hX
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at he
  have he' : (regressionMap w X).mulVec (Y-X.mulVec b) = 0 := by
    simpa only [regressionMap, Matrix.mul_assoc] using he
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] at he'
  exact sub_eq_zero.mp he'

namespace CollapsedControlsCertificates
attribute [-instance] Classical.propDecidable

/-- The rational version of the specified design mass. -/
def rate : Fin 4 → ℚ := ![1/10,1/5,3/10,2/5]
def d (i : Fin 4 × Fin 2) : ℚ :=
  (1/2)*(if i.2=0 then rate i.1 else 1-rate i.1)
def pi (i : Fin 4 × Fin 2) (k : Fin 4) : ℚ :=
  if k=0 ∨ k=1 then 1/4 else if k=2 then 1/2-d i else d i
def mass (z : Fin 6 × (Fin 4 → Bool)) : ℚ :=
  (1/6)*∏ j, if j∈controlPair z.1 then
    (if z.2 j then rate j else 1-rate j) else 1/2

lemma counts : ∀ z : Fin 6 × (Fin 4 → Bool), ∀ k : Fin 4,
    (Finset.univ.filter (fun i => controlExposure z i=k)).card=2 := by
  decide +kernel
lemma positive : ∀ z : Fin 6 × (Fin 4 → Bool), 0 < mass z := by
  decide +kernel
lemma total : (∑ z, mass z)=1 := by
  decide +kernel
lemma marginals : ∀ i : Fin 4 × Fin 2, ∀ k : Fin 4,
    (∑ z, mass z*(if controlExposure z i=k then (1:ℚ) else 0))=pi i k := by
  decide +kernel

end CollapsedControlsCertificates

lemma collapsedControls_rate_cast (j : Fin 4) :
    (CollapsedControlsCertificates.rate j : ℝ) = pairReferentRate j := by
  fin_cases j <;> norm_num [CollapsedControlsCertificates.rate, pairReferentRate]
lemma collapsedControls_d_cast (i : Fin 4 × Fin 2) :
    (CollapsedControlsCertificates.d i : ℝ) = controlPiI i := by
  simp [CollapsedControlsCertificates.d, controlPiI, collapsedControls_rate_cast,
    apply_ite (fun q : ℚ => (q:ℝ))]
lemma collapsedControls_pi_cast (i : Fin 4 × Fin 2) (k : Fin 4) :
    (CollapsedControlsCertificates.pi i k : ℝ) = controlPi i k := by
  simp [CollapsedControlsCertificates.pi, controlPi, collapsedControls_d_cast,
    apply_ite (fun q : ℚ => (q:ℝ))]
lemma collapsedControls_mass_cast (z : Fin 6 × (Fin 4 → Bool)) :
    (CollapsedControlsCertificates.mass z : ℝ) = controlMass z := by
  simp [CollapsedControlsCertificates.mass, controlMass, collapsedControls_rate_cast,
    Rat.cast_prod, apply_ite (fun q : ℚ => (q:ℝ))]

lemma collapsedControls_total : (∑ z, controlMass z)=1 := by
  have h := congrArg (fun q : ℚ => (q:ℝ)) CollapsedControlsCertificates.total
  simpa only [Rat.cast_sum, collapsedControls_mass_cast, Rat.cast_one] using h
lemma collapsedControls_positive (z : Fin 6 × (Fin 4 → Bool)) : 0 < controlMass z := by
  rw [← collapsedControls_mass_cast]
  exact_mod_cast CollapsedControlsCertificates.positive z
lemma collapsedControls_marginals (i : Fin 4 × Fin 2) (k : Fin 4) :
    (∑ z, controlMass z*(if controlExposure z i=k then (1:ℝ) else 0))=controlPi i k := by
  have h := congrArg (fun q : ℚ => (q:ℝ)) (CollapsedControlsCertificates.marginals i k)
  simpa [Rat.cast_sum, collapsedControls_mass_cast, collapsedControls_pi_cast,
    apply_ite (fun q : ℚ => (q:ℝ))] using h

lemma collapsedControls_weight_positive (D : (Fin 4 × Fin 2) → Fin 4)
    (i : Fin 4 × Fin 2) : 0 < controlWeight D i := by
  rcases i with ⟨i,j⟩
  unfold controlWeight
  apply one_div_pos.mpr
  generalize D (i,j) = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [controlPi, controlPiI, pairReferentRate]

lemma collapsedControls_d_injective : Function.Injective controlPiI := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [controlPiI, pairReferentRate] at *

lemma collapsedControls_prediction (D : (Fin 4 × Fin 2) → Fin 4)
    (v : Fin 5 → ℝ) (i : Fin 4 × Fin 2) :
    (controlFullRow D).mulVec v i = v (D i).castSucc + controlPiI i * v 4 := by
  have h := RegressionCompletion.pooled_prediction (p:=1) D (fun i => ![controlPiI i]) v i
  have hc : (D i).castAdd 1 = (D i).castSucc := Fin.ext rfl
  simpa [controlFullRow, Fin.sum_univ_succ, hc] using h

lemma collapsedControls_rank_of_counts (D : (Fin 4 × Fin 2) → Fin 4)
    (hc : ∀ k, (Finset.univ.filter (fun i => D i=k)).card=2) :
    Function.Injective (controlFullRow D).mulVec := by
  intro a b hab
  have hv (i : Fin 4 × Fin 2) :
      a (D i).castSucc + controlPiI i * a 4 =
        b (D i).castSucc + controlPiI i * b 4 := by
    simpa only [collapsedControls_prediction] using congrFun hab i
  obtain ⟨u,v,huv,hs⟩ := Finset.card_eq_two.mp (hc 0)
  have hum : u ∈ Finset.univ.filter (fun i => D i=0) := by rw [hs]; simp
  have hvm : v ∈ Finset.univ.filter (fun i => D i=0) := by rw [hs]; simp
  have hu : D u=0 := (Finset.mem_filter.mp hum).2
  have hv' : D v=0 := (Finset.mem_filter.mp hvm).2
  have hd : controlPiI u - controlPiI v ≠ 0 :=
    sub_ne_zero.mpr (fun h => huv (collapsedControls_d_injective h))
  have ha4 : a 4=b 4 := by
    have e1 := hv u
    have e2 := hv v
    rw [hu] at e1
    rw [hv'] at e2
    have he : (controlPiI u-controlPiI v)*(a 4-b 4)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hd)
  have he (k : Fin 4) : a k.castSucc=b k.castSucc := by
    have hn : 0 < (Finset.univ.filter (fun i => D i=k)).card := by rw [hc]; decide
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hn
    have hi' := (Finset.mem_filter.mp hi).2
    have e := hv i
    rw [hi', ha4] at e
    exact add_right_cancel e
  ext j
  fin_cases j
  · exact he 0
  · exact he 1
  · exact he 2
  · exact he 3
  · exact ha4

lemma collapsedControls_rank (z : Fin 6 × (Fin 4 → Bool)) :
    Function.Injective (controlFullRow (controlExposure z)).mulVec :=
  collapsedControls_rank_of_counts _ (CollapsedControlsCertificates.counts z)

lemma collapsedControls_observed_counts (k : Fin 4) :
    (Finset.univ.filter (fun i => controlObserved i=k)).card=2 := by
  revert k
  decide +kernel

lemma collapsedControls_observed_rank :
    Function.Injective (controlFullRow controlObserved).mulVec :=
  collapsedControls_rank_of_counts _ collapsedControls_observed_counts

lemma collapsedControls_point : controlPoint=![1/13,-2,-14/3,-23/39,180/13] := by
  apply collapsedControls_fit_of_normal _ _ _ _
    (collapsedControls_weight_positive _) collapsedControls_observed_rank
  intro k
  simp only [collapsedControls_prediction]
  fin_cases k <;>
    norm_num [controlWeight, controlPi, controlPiI,
      pairReferentRate, controlY, controlObserved, controlFullRow, pooledExposureRow,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma collapsedControls_means (k : Fin 4) :
    controlPointMean k=(![46/13,19/13,-47/39,112/39] : Fin 4 → ℝ) k := by
  fin_cases k <;> norm_num [controlPointMean, collapsedControls_point]

lemma collapsedControls_imputation (z : Fin 6 × (Fin 4 → Bool)) :
    controlContrast z true
      (fun i => controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i))=
        controlContrast z true controlResidual+controlPointMean 3-controlPointMean 2 := by
  let X := controlFullRow (controlExposure z)
  let L := regressionMap (controlWeight (controlExposure z)) X
  have hleft : L*X=1 := RegressionCompletion.weighted_left_inverse _ _
    (collapsedControls_weight_positive _) (collapsedControls_rank z)
  have himp :
      (fun i => controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i)) =
      controlResidual+X.mulVec controlPoint := by
    ext i
    change controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i) =
      (controlY i-(controlFullRow controlObserved).mulVec controlPoint i)+
        (controlFullRow (controlExposure z)).mulVec controlPoint i
    rw [collapsedControls_prediction, collapsedControls_prediction]
    simp only [controlPointMean]
    ring
  have hf : L.mulVec
      (fun i => controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i)) =
      L.mulVec controlResidual+controlPoint := by
    rw [himp, Matrix.mulVec_add, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  change L.mulVec _ 3-L.mulVec _ 2 =
    (L.mulVec controlResidual 3-L.mulVec controlResidual 2)+controlPointMean 3-controlPointMean 2
  rw [hf]
  simp [Pi.add_apply, controlPointMean, Fin.castSucc]
  ring

namespace CollapsedControlsCertificates
attribute [-instance] Classical.propDecidable

/-- Exact residuals of the observed inverse-form fit, in unit order. -/
def residual : (Fin 4 × Fin 2) → ℚ :=
  fun i => ![![-4/39,17/39],![8/39,-34/39],![11/13,-24/13],![-11/13,24/13]] i.1 i.2

def weight (z : Fin 6 × (Fin 4 → Bool)) (i : Fin 4 × Fin 2) : ℚ :=
  1/pi i (controlExposure z i)
def row (z : Fin 6 × (Fin 4 → Bool)) : Matrix (Fin 4 × Fin 2) (Fin 5) ℚ :=
  fun i j => if h : j.val<4 then
    (if controlExposure z i=⟨j.val,h⟩ then 1 else 0) else d i
def collapsedRow (z : Fin 6 × (Fin 4 → Bool)) : Matrix (Fin 4 × Fin 2) (Fin 4) ℚ :=
  fun i k => if controlExposure z i=k then 1 else 0

/-- Within-exposure sufficient statistics, computed over the actual eight units. -/
def W (z : Fin 6 × (Fin 4 → Bool)) (k : Fin 4) : ℚ :=
  ∑ i, if controlExposure z i=k then weight z i else 0
def dbar (z : Fin 6 × (Fin 4 → Bool)) (k : Fin 4) : ℚ :=
  (∑ i, if controlExposure z i=k then weight z i*d i else 0)/W z k
def rbar (z : Fin 6 × (Fin 4 → Bool)) (k : Fin 4) : ℚ :=
  (∑ i, if controlExposure z i=k then weight z i*residual i else 0)/W z k
def slope (z : Fin 6 × (Fin 4 → Bool)) : ℚ :=
  (∑ i, weight z i*(d i-dbar z (controlExposure z i))*residual i)/
    (∑ i, weight z i*(d i-dbar z (controlExposure z i))^2)
def fullFit (z : Fin 6 × (Fin 4 → Bool)) : Fin 5 → ℚ :=
  ![rbar z 0-slope z*dbar z 0,rbar z 1-slope z*dbar z 1,
    rbar z 2-slope z*dbar z 2,rbar z 3-slope z*dbar z 3,slope z]
def fullContrast (z : Fin 6 × (Fin 4 → Bool)) : ℚ := fullFit z 3-fullFit z 2
def collapsedContrast (z : Fin 6 × (Fin 4 → Bool)) : ℚ := rbar z 3-rbar z 2

/-- These are certificates for normal equations, not assumed fitted outputs. -/
lemma full_normal : ∀ z : Fin 6 × (Fin 4 → Bool), ∀ k : Fin 5,
    (∑ i, weight z i*(residual i-(row z).mulVec (fullFit z) i)*row z i k)=0 := by
  decide +kernel
lemma collapsed_normal : ∀ z : Fin 6 × (Fin 4 → Bool), ∀ k : Fin 4,
    (∑ i, weight z i*(residual i-(collapsedRow z).mulVec (rbar z) i)*collapsedRow z i k)=0 := by
  decide +kernel

/-- Six sixteen-orientation sums, using the specified mass including its factor 1/6. -/
lemma full_first_sub : ∀ a : Fin 6,
    (∑ b : Fin 4 → Bool, mass (a,b)*fullContrast (a,b)) =
      (![5568738611536457/10408544638154910, -7385141/131594385,
        203449256583257/1305220814599650, -173831896063/1365313285050,
        37273/4001920, 1403817546767657/84467209164293670] : Fin 6 → ℚ) a := by
  decide +kernel
lemma full_second_sub : ∀ a : Fin 6,
    (∑ b : Fin 4 → Bool, mass (a,b)*(fullContrast (a,b))^2) =
      (![17332055767680513723877465077605/3250134044533899790313074713243,
        461437954376604991/646504400771720400,
        33111763007675144103735477449/28393356247736231976496335375,
        73230724746135708760631/93204018316701127675125,
        40908628483787/72069136588800,
        30809326889074782813983956535693/34974065803943806615325833343475] : Fin 6 → ℚ) a := by
  decide +kernel
lemma collapsed_first_sub : ∀ a : Fin 6,
    (∑ b : Fin 4 → Bool, mass (a,b)*collapsedContrast (a,b)) =
      (![-5453/328185,-189/4160,2351/42250,-44177/482625,-7/4680,-23/1014] : Fin 6 → ℚ) a := by
  decide +kernel
lemma collapsed_second_sub : ∀ a : Fin 6,
    (∑ b : Fin 4 → Bool, mass (a,b)*(collapsedContrast (a,b))^2) =
      (![65436364/1436071923,840301/2163200,3434563/7140250,
        305935028/621138375,1403507/3650400,96253/171366] : Fin 6 → ℚ) a := by
  decide +kernel

lemma full_first : (∑ z, mass z*fullContrast z) =
    1525583388999673370335049882571277362965555386891/
      2860206147359563648614743196394330930461724348800 := by
  rw [Fintype.sum_prod_type]
  simp_rw [full_first_sub]
  norm_num [Fin.sum_univ_succ]
lemma full_second : (∑ z, mass z*(fullContrast z)^2) =
    162294242395623124085856811887281695046496895355999591327792546204587891024266577482308221706275643/
      17179636331326219642795174042195480651251443662217762571380859191569288708444680898777046529024000 := by
  rw [Fintype.sum_prod_type]
  simp_rw [full_second_sub]
  norm_num [Fin.sum_univ_succ]
lemma collapsed_first : (∑ z, mass z*collapsedContrast z) = -55573103/455083200 := by
  rw [Fintype.sum_prod_type]
  simp_rw [collapsed_first_sub]
  norm_num [Fin.sum_univ_succ]
lemma collapsed_second : (∑ z, mass z*(collapsedContrast z)^2) =
    36559496963923907/15532553919168000 := by
  rw [Fintype.sum_prod_type]
  simp_rw [collapsed_second_sub]
  norm_num [Fin.sum_univ_succ]

end CollapsedControlsCertificates

lemma collapsedControls_residual_cast (i : Fin 4 × Fin 2) :
    (CollapsedControlsCertificates.residual i : ℝ) = controlResidual i := by
  simp only [controlResidual, Pi.sub_apply, collapsedControls_prediction, collapsedControls_point]
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [CollapsedControlsCertificates.residual, controlY, controlObserved,
      controlPiI, pairReferentRate]

lemma collapsedControls_weight_cast (z : Fin 6 × (Fin 4 → Bool)) (i : Fin 4 × Fin 2) :
    (CollapsedControlsCertificates.weight z i : ℝ) = controlWeight (controlExposure z) i := by
  simp [CollapsedControlsCertificates.weight, controlWeight, collapsedControls_pi_cast]

lemma collapsedControls_row_cast (z : Fin 6 × (Fin 4 → Bool))
    (i : Fin 4 × Fin 2) (j : Fin 5) :
    (CollapsedControlsCertificates.row z i j : ℝ) = controlFullRow (controlExposure z) i j := by
  fin_cases j <;> simp [CollapsedControlsCertificates.row, controlFullRow, pooledExposureRow,
    collapsedControls_d_cast, apply_ite (fun q : ℚ => (q:ℝ))]

lemma collapsedControls_collapsed_rank (z : Fin 6 × (Fin 4 → Bool)) :
    Function.Injective (Matrix.mulVec
      (fun i k => if controlExposure z i=k then (1:ℝ) else 0 :
        Matrix (Fin 4 × Fin 2) (Fin 4) ℝ)) := by
  intro a b h
  ext k
  have hn : 0 < (Finset.univ.filter (fun i => controlExposure z i=k)).card := by
    rw [CollapsedControlsCertificates.counts]; decide
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hn
  have hi' := (Finset.mem_filter.mp hi).2
  have he := congrFun h i
  simpa [Matrix.mulVec, dotProduct, hi'] using he

lemma collapsedControls_full_fit (z : Fin 6 × (Fin 4 → Bool)) :
    (regressionMap (controlWeight (controlExposure z))
      (controlFullRow (controlExposure z))).mulVec controlResidual =
      fun k => (CollapsedControlsCertificates.fullFit z k : ℝ) := by
  apply collapsedControls_fit_of_normal _ _ _ _
    (collapsedControls_weight_positive _) (collapsedControls_rank z)
  intro k
  have h := congrArg (fun q : ℚ => (q:ℝ)) (CollapsedControlsCertificates.full_normal z k)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_zero, collapsedControls_weight_cast, collapsedControls_row_cast,
    collapsedControls_residual_cast] using h

lemma collapsedControls_collapsed_fit (z : Fin 6 × (Fin 4 → Bool)) :
    (regressionMap (controlWeight (controlExposure z))
      (fun i k => if controlExposure z i=k then (1:ℝ) else 0 :
        Matrix (Fin 4 × Fin 2) (Fin 4) ℝ)).mulVec controlResidual =
      fun k => (CollapsedControlsCertificates.rbar z k : ℝ) := by
  apply collapsedControls_fit_of_normal _ _ _ _
    (collapsedControls_weight_positive _) (collapsedControls_collapsed_rank z)
  intro k
  have h := congrArg (fun q : ℚ => (q:ℝ)) (CollapsedControlsCertificates.collapsed_normal z k)
  simpa [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_zero, collapsedControls_weight_cast, CollapsedControlsCertificates.collapsedRow,
    apply_ite (fun q : ℚ => (q:ℝ)), collapsedControls_residual_cast] using h

lemma collapsedControls_full_contrast (z : Fin 6 × (Fin 4 → Bool)) :
    controlContrast z true controlResidual = (CollapsedControlsCertificates.fullContrast z : ℝ) := by
  change (regressionMap _ _).mulVec controlResidual 3-
    (regressionMap _ _).mulVec controlResidual 2 = _
  rw [collapsedControls_full_fit]
  simp only [CollapsedControlsCertificates.fullContrast, Rat.cast_sub]

lemma collapsedControls_collapsed_contrast (z : Fin 6 × (Fin 4 → Bool)) :
    controlContrast z false controlResidual = (CollapsedControlsCertificates.collapsedContrast z : ℝ) := by
  change (regressionMap _ _).mulVec controlResidual 3-
    (regressionMap _ _).mulVec controlResidual 2 = _
  rw [collapsedControls_collapsed_fit]
  simp only [CollapsedControlsCertificates.collapsedContrast, Rat.cast_sub]

lemma collapsedControls_cast_sq (q : ℚ) : ((q^2 : ℚ) : ℝ) = (q:ℝ)^2 := by
  simp only [pow_two, Rat.cast_mul]

lemma collapsedControls_full_variance :
    controlVariance (fun z => controlContrast z true controlResidual)=controlFullVarianceCertificate := by
  have h1 := congrArg (fun q : ℚ => (q:ℝ)) CollapsedControlsCertificates.full_first
  have h2 := congrArg (fun q : ℚ => (q:ℝ)) CollapsedControlsCertificates.full_second
  norm_num only [Rat.cast_sum, Rat.cast_mul, collapsedControls_cast_sq, Rat.cast_div, Rat.cast_ofNat,
    collapsedControls_mass_cast, ← collapsedControls_full_contrast] at h1 h2
  unfold controlVariance
  rw [h1,h2]
  norm_num [controlFullVarianceCertificate]

lemma collapsedControls_collapsed_variance :
    controlVariance (fun z => controlContrast z false controlResidual)=controlCollapsedVarianceCertificate := by
  have h1 := congrArg (fun q : ℚ => (q:ℝ)) CollapsedControlsCertificates.collapsed_first
  have h2 := congrArg (fun q : ℚ => (q:ℝ)) CollapsedControlsCertificates.collapsed_second
  norm_num only [Rat.cast_sum, Rat.cast_mul, collapsedControls_cast_sq, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_neg, collapsedControls_mass_cast, ← collapsedControls_collapsed_contrast] at h1 h2
  unfold controlVariance
  rw [h1,h2]
  norm_num [controlCollapsedVarianceCertificate]

theorem collapsed_controls_variance_counterexample_proof :
    Fintype.card (Fin 6 × (Fin 4 → Bool))=96 ∧
    (∑ z, controlMass z)=1 ∧ (∀ z, 0<controlMass z) ∧
    (∀ z k, (Finset.univ.filter (fun i => controlExposure z i=k)).card=2) ∧
    (∀ i k, (∑ z, controlMass z*(if controlExposure z i=k then (1:ℝ) else 0))=controlPi i k) ∧
    (∀ z, Function.Injective (controlFullRow (controlExposure z)).mulVec) ∧
    controlPoint=![1/13,-2,-14/3,-23/39,180/13] ∧
    (∀ k, controlPointMean k=(![46/13,19/13,-47/39,112/39] : Fin 4 → ℝ) k) ∧
    (∀ z,
      controlContrast z true (fun i => controlY i+controlPointMean (controlExposure z i)-controlPointMean (controlObserved i))=
        controlContrast z true controlResidual+controlPointMean 3-controlPointMean 2) ∧
    controlVariance (fun z => controlContrast z true controlResidual)=controlFullVarianceCertificate ∧
    controlVariance (fun z => controlContrast z false controlResidual)=controlCollapsedVarianceCertificate ∧
    9<controlFullVarianceCertificate ∧ controlFullVarianceCertificate<37/4 ∧
    2<controlCollapsedVarianceCertificate ∧ controlCollapsedVarianceCertificate<5/2 := by
  refine ⟨?_, collapsedControls_total, collapsedControls_positive,
    CollapsedControlsCertificates.counts, collapsedControls_marginals, collapsedControls_rank,
    collapsedControls_point, collapsedControls_means, collapsedControls_imputation,
    collapsedControls_full_variance, collapsedControls_collapsed_variance, ?_⟩
  · norm_num [Fintype.card_fun]
  · exact ⟨collapsed_controls_certificate_inequalities.1,
      collapsed_controls_certificate_inequalities.2.1,
      collapsed_controls_certificate_inequalities.2.2.1,
      collapsed_controls_certificate_inequalities.2.2.2.1⟩

end AronowAudit.P037.Wave1
