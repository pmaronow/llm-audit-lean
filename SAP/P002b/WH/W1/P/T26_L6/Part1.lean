import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace SAP.P002b.WH.W1.P.T26_L6

open SAP.P002b SAP.P002b.WH.W1
open scoped BigOperators ENNReal Matrix
attribute [local instance] Classical.propDecidable
noncomputable section

def wx (i : Fin 8) : ℝ := 2*(i.val:ℝ)-7
def wxc (i : Fin 8) (j : Fin 1) : ℝ := wx i

def oe : Fin 2 ≃ Option (Fin 1) where
 toFun i := if i.val=0 then none else some 0
 invFun | none => 0 | some _ => 1
 left_inv := by intro i; fin_cases i <;> rfl
 right_inv := by intro i; cases i with | none => rfl | some j => fin_cases j <;> rfl
lemma det_formula (A : Finset (Fin 8)) (hA : A.Nonempty) :
  (gram (n:=8) (k:=1) wxc A).det = groupMean A (fun i => wx i^2) - (groupMean A wx)^2 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  rw [← Matrix.det_submatrix_equiv_self oe (gram (n:=8) (k:=1) wxc A)]
  rw [Matrix.det_fin_two]
  simp [Matrix.submatrix_apply, gram, groupMean, augmented, oe, wxc]
  field_simp [hcard]
  <;> ring
lemma centered_mean (A : Finset (Fin 8)) (hA : A.Nonempty) :
  groupMean A (fun i => (wx i - groupMean A wx)^2) =
    groupMean A (fun i => wx i^2) - (groupMean A wx)^2 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  let m := groupMean A wx
  have hs : (∑ i ∈ A, wx i) = (A.card : ℝ) * m := by dsimp [m, groupMean]; field_simp [hcard]
  have hsum : (∑ i ∈ A, (wx i - m)^2) =
      (∑ i ∈ A, wx i^2) - 2*m*(∑ i ∈ A, wx i) + (A.card:ℝ)*m^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const]
    simp only [nsmul_eq_mul]
    have hterm : (∑ i ∈ A, wx i * m) = (∑ i ∈ A, wx i) * m := by rw [Finset.sum_mul]
    have hfactor : ∀ i, 2 * wx i * m = 2 * (wx i * m) := by intro i; ring
    simp_rw [hfactor]
    rw [← Finset.mul_sum, hterm]
    ring
  rw [show groupMean A wx = m by rfl]
  simp only [groupMean]
  rw [hsum, hs]
  field_simp [hcard]
  <;> ring
lemma det_pos (A : Finset (Fin 8)) (hcard : A.card = 4) : 0 < (gram (n:=8) (k:=1) wxc A).det := by
  have hA : A.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hcard
  rw [det_formula A hA, ← centered_mean A hA]
  change 0 < (∑ i ∈ A, (wx i - groupMean A wx)^2) / (A.card:ℝ)
  have hx : ∃ i ∈ A, wx i - groupMean A wx ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp (by rw [hcard]; norm_num)
    have heq : wx i = wx j := by linarith [hn i hi, hn j hj]
    have hv : i.val = j.val := by
      apply_fun (fun z : ℝ => (z + 7) / 2) at heq
      dsimp [wx] at heq
      norm_num at heq
      exact_mod_cast heq
    exact hij (Fin.ext hv)
  obtain ⟨i, hi, hne⟩ := hx
  have hs : 0 < ∑ i ∈ A, (wx i - groupMean A wx)^2 :=
    Finset.sum_pos' (fun j hj => sq_nonneg _) ⟨i, hi, sq_pos_of_ne_zero hne⟩
  positivity

def momentXY (A : Finset (Fin 8)) (q : Fin 8 → ℝ) := groupMean A (fun i => wx i * q i)
def momentXX (A : Finset (Fin 8)) := groupMean A (fun i => wx i^2)
def momentX (A : Finset (Fin 8)) := groupMean A wx
def momentY (A : Finset (Fin 8)) (q : Fin 8 → ℝ) := groupMean A q
def fitSlope (A : Finset (Fin 8)) (q : Fin 8 → ℝ) :=
  (momentXY A q - momentX A * momentY A q) / (momentXX A - (momentX A)^2)
def fitIntercept (A : Finset (Fin 8)) (q : Fin 8 → ℝ) := momentY A q - fitSlope A q * momentX A

theorem ols_fit (A : Finset (Fin 8)) (q : Fin 8 → ℝ) (hA : A.Nonempty)
    (hdet : (gram (n:=8) (k:=1) wxc A).det ≠ 0) :
    ols (n:=8) (k:=1) wxc A q = fun | none => fitIntercept A q | some _ => fitSlope A q := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have hden : momentXX A - (momentX A)^2 ≠ 0 := by
    change groupMean A (fun i => wx i ^ 2) - (groupMean A wx)^2 ≠ 0
    rw [← det_formula A hA]
    change (gram wxc A).det ≠ 0
    exact hdet
  let c : Option (Fin 1) → ℝ := fun | none => fitIntercept A q | some _ => fitSlope A q
  have h00 : gram wxc A none none = 1 := by simp [gram, groupMean, augmented, hcard, wxc]
  have h01 : gram wxc A none (some 0) = momentX A := by simp [gram, augmented, momentX, wxc]
  have h10 : gram wxc A (some 0) none = momentX A := by simp [gram, augmented, momentX, mul_comm, wxc]
  have h11 : gram wxc A (some 0) (some 0) = momentXX A := by simp [gram, augmented, momentXX, pow_two, wxc]
  have hs0 : score wxc A q none = momentY A q := by simp [score, augmented, momentY, wxc]
  have hs1 : score wxc A q (some 0) = momentXY A q := by simp [score, augmented, momentXY, wxc]
  have hc : gram wxc A *ᵥ c = score wxc A q := by
    ext z
    cases z with
    | none => simp [Matrix.mulVec, dotProduct, Fintype.sum_option, c, h00, h01, hs0, fitIntercept]; ring
    | some j =>
      fin_cases j
      simp [Matrix.mulVec, dotProduct, Fintype.sum_option, c, h10, h11, hs1, fitIntercept]
      dsimp [fitSlope]
      field_simp [hden]
      <;> ring
  have hn := AronowAudit.P002.ols_normal_equations (fun i j => wx i) A q hdet
  have heq : ols (n:=8) (k:=1) wxc A q = c :=
    (Matrix.mulVec_injective_of_det_ne_zero hdet) (hn.trans hc.symm)
  simpa [c] using heq

def qX (i : Fin 8) : ℚ := 2*i.val-7
def qY (i : Fin 8) : ℚ := ![(-4:ℚ),0,2,-2,2,-6,-4,6] i
def qD (i : Fin 8) : ℚ := ![(0:ℚ),1,0,0,0,1,1,1] i
def rsum (A : Finset (Fin 8)) (comp : Bool) (f : Fin 8 → ℚ) : ℚ :=
 if comp then (∑ i, f i) - (∑ i ∈ A, f i) else (∑ i ∈ A, f i)
def rcard (A : Finset (Fin 8)) (comp : Bool) : ℕ := if comp then 8-A.card else A.card
def rmean (A : Finset (Fin 8)) (comp : Bool) (q : Fin 8 → ℚ) : ℚ := rsum A comp q / rcard A comp
def rslope (A : Finset (Fin 8)) (comp : Bool) (q : Fin 8 → ℚ) : ℚ :=
 (rmean A comp (fun i => qX i*q i)-rmean A comp qX*rmean A comp q) /
 (rmean A comp (fun i=>qX i^2)-(rmean A comp qX)^2)
def rintercept (A : Finset (Fin 8)) (comp : Bool) (q : Fin 8 → ℚ) : ℚ :=
 rmean A comp q-rslope A comp q*rmean A comp qX
def rrss (A : Finset (Fin 8)) (comp : Bool) (q : Fin 8 → ℚ) : ℚ :=
 rsum A comp (fun i => (q i-rintercept A comp q-rslope A comp q*qX i)^2)

lemma qX_cast (i : Fin 8) : (qX i : ℝ) = wx i := by norm_num [qX, wx]
lemma rsum_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ) :
  (rsum A c q : ℝ) = ∑ i ∈ (if c then Aᶜ else A), (q i : ℝ) := by
  cases c with
  | false => simp [rsum, Rat.cast_sum]
  | true =>
    simp only [rsum, if_pos, Rat.cast_sub, Rat.cast_sum]
    rw [← Finset.sum_add_sum_compl A (fun i => (q i : ℝ))]
    ring
lemma rcard_cast (A : Finset (Fin 8)) (c : Bool) :
  (rcard A c : ℝ) = (if c then (Aᶜ.card : ℝ) else (A.card : ℝ)) := by
  cases c <;> simp [rcard, Finset.card_compl]
lemma rmean_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ) :
  (rmean A c q : ℝ) = groupMean (if c then Aᶜ else A) (fun i => (q i : ℝ)) := by
  unfold rmean groupMean
  push_cast
  rw [rsum_cast, rcard_cast]
  split_ifs <;> rfl
lemma rslope_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ) :
  (rslope A c q : ℝ) = fitSlope (if c then Aᶜ else A) (fun i => (q i : ℝ)) := by
  unfold rslope fitSlope momentXY momentXX momentX momentY
  push_cast
  rw [rmean_cast A c (fun i => qX i*q i), rmean_cast A c q,
      rmean_cast A c qX, rmean_cast A c (fun i => qX i^2)]
  simp [qX_cast]
lemma rintercept_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ) :
  (rintercept A c q : ℝ) = fitIntercept (if c then Aᶜ else A) (fun i => (q i : ℝ)) := by
  unfold rintercept fitIntercept momentY momentX
  push_cast
  rw [rmean_cast A c q, rslope_cast, rmean_cast A c qX]
  simp [qX_cast]
lemma rrss_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ) :
    (rrss A c q : ℝ) = rss wxc (if c then Aᶜ else A) (fun i => (q i : ℝ))
      (fun z => match z with
        | none => fitIntercept (if c then Aᶜ else A) (fun i => (q i : ℝ))
        | some _ => fitSlope (if c then Aᶜ else A) (fun i => (q i : ℝ))) := by
  have hc : ∀ i, ((q i-rintercept A c q-rslope A c q*qX i)^2:ℝ) =
      ((q i:ℝ)-fitIntercept (if c then Aᶜ else A) (fun i => (q i:ℝ))-
        fitSlope (if c then Aᶜ else A) (fun i => (q i:ℝ))*wx i)^2 := by
    intro i
    push_cast
    rw [rintercept_cast, rslope_cast, qX_cast]
  unfold rrss rss
  rw [rsum_cast]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  rw [hc i]
  simp [dotProduct, Fintype.sum_option, augmented, wxc]
  <;> ring

def rTau (A : Finset (Fin 8)) (q : Fin 8 → ℚ) : ℚ := rintercept A false q-rintercept A true q
def rVariance (A : Finset (Fin 8)) (q : Fin 8 → ℚ) : ℚ := (rrss A false q+rrss A true q)/16

def qreal (q : Fin 8 → ℚ) : Fin 8 → ℝ := fun i => (q i : ℝ)
lemma witness_x_eq : intervalWitnessPopulation.x = wxc := by
  funext i
  funext j
  fin_cases j
  norm_num [intervalWitnessPopulation, wxc, wx]

lemma rss_actual_cast (A : Finset (Fin 8)) (c : Bool) (q : Fin 8 → ℚ)
    (hA : (if c then Aᶜ else A).Nonempty)
    (hdet : (gram wxc (if c then Aᶜ else A)).det ≠ 0) :
    rss intervalWitnessPopulation.x (if c then Aᶜ else A) (qreal q)
      (ols intervalWitnessPopulation.x (if c then Aᶜ else A) (qreal q)) =
      (rrss A c q : ℝ) := by
  rw [witness_x_eq, ols_fit (if c then Aᶜ else A) (qreal q) hA hdet]
  exact (rrss_cast A c q).symm

lemma tau_actual_cast (A : Finset (Fin 8)) (q : Fin 8 → ℚ)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hdet : (gram wxc A).det ≠ 0) (hdetc : (gram wxc Aᶜ).det ≠ 0) :
    adjustedTau intervalWitnessPopulation (qreal q) A = (rTau A q : ℝ) := by
  have h1 := arm_adjusted_mean intervalWitnessPopulation.x A (qreal q) hA hdet
  have h0 := arm_adjusted_mean intervalWitnessPopulation.x Aᶜ (qreal q) hAc hdetc
  change groupMean A (fun i => qreal q i - slopeDot (intervalWitnessPopulation.x i) (ols intervalWitnessPopulation.x A (qreal q))) -
    groupMean Aᶜ (fun i => qreal q i - slopeDot (intervalWitnessPopulation.x i) (ols intervalWitnessPopulation.x Aᶜ (qreal q))) = _
  rw [h1, h0]
  rw [witness_x_eq, ols_fit A (qreal q) hA hdet, ols_fit Aᶜ (qreal q) hAc hdetc]
  change fitIntercept A (qreal q) - fitIntercept Aᶜ (qreal q) = _
  change fitIntercept A (fun i => (q i:ℝ)) - fitIntercept Aᶜ (fun i => (q i:ℝ)) = _
  have hif : (rintercept A false q:ℝ) = fitIntercept A (fun i => (q i:ℝ)) := by
    change (rintercept A false q:ℝ) = fitIntercept A (fun i => (q i:ℝ))
    exact rintercept_cast A false q
  have hic : (rintercept A true q:ℝ) = fitIntercept Aᶜ (fun i => (q i:ℝ)) := by
    change (rintercept A true q:ℝ) = fitIntercept Aᶜ (fun i => (q i:ℝ))
    exact rintercept_cast A true q
  rw [← hif, ← hic]
  simp [rTau]

lemma rrss_cast_false (A : Finset (Fin 8)) (q : Fin 8 → ℚ) :
    (rrss A false q : ℝ) = rss wxc A (qreal q) (fun z => match z with
      | none => fitIntercept A (qreal q)
      | some _ => fitSlope A (qreal q)) := by
  change (rrss A false q : ℝ) = rss wxc A (fun i => (q i:ℝ)) (fun z => match z with
    | none => fitIntercept A (fun i => (q i:ℝ))
    | some _ => fitSlope A (fun i => (q i:ℝ)))
  simpa using rrss_cast A false q
lemma rrss_cast_true (A : Finset (Fin 8)) (q : Fin 8 → ℚ) :
    (rrss A true q : ℝ) = rss wxc Aᶜ (qreal q) (fun z => match z with
      | none => fitIntercept Aᶜ (qreal q)
      | some _ => fitSlope Aᶜ (qreal q)) := by
  change (rrss A true q : ℝ) = rss wxc Aᶜ (fun i => (q i:ℝ)) (fun z => match z with
    | none => fitIntercept Aᶜ (fun i => (q i:ℝ))
    | some _ => fitSlope Aᶜ (fun i => (q i:ℝ)))
  simpa using rrss_cast A true q

lemma variance_actual_cast (A : Finset (Fin 8)) (q : Fin 8 → ℚ)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hdet : (gram wxc A).det ≠ 0) (hdetc : (gram wxc Aᶜ).det ≠ 0) :
    adjustedSigma2 intervalWitnessPopulation (qreal q) A = (rVariance A q : ℝ) := by
  unfold adjustedSigma2
  simp only [fitted]
  rw [witness_x_eq]
  norm_num [intervalWitnessPopulation, controlSize]
  rw [ols_fit A (qreal q) hA hdet, ols_fit Aᶜ (qreal q) hAc hdetc]
  rw [← rrss_cast_false A q, ← rrss_cast_true A q]
  unfold rVariance
  push_cast
  <;> ring

lemma observedW_cast (b : ℚ) :
    observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment =
      qreal (fun i => qY i-b*qD i) := by
  funext i
  fin_cases i <;> norm_num [observedW, observedY, observedD, intervalWitnessPopulation,
    intervalWitnessAssignment, binary, qY, qD, qreal]
def rScore (A : Finset (Fin 8)) (q : Fin 8 → ℚ) : ℚ := (rTau A q)^2/rVariance A q
lemma rScore_cast (A : Finset (Fin 8)) (q : Fin 8 → ℚ) :
    (rScore A q : ℝ) = (rTau A q:ℝ)^2/(rVariance A q:ℝ) := by
  norm_num [rScore, rTau, rVariance, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_sub]
lemma stat_cast (A : Finset (Fin 8)) (q : Fin 8 → ℚ)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hdet : (gram wxc A).det ≠ 0) (hdetc : (gram wxc Aᶜ).det ≠ 0)
    (hvar : 0 < rVariance A q) :
    adjustedAR intervalWitnessPopulation (qreal q) A =
      ENNReal.ofReal (Real.sqrt (rScore A q:ℝ)) := by
  rw [adjustedAR, tau_actual_cast A q hA hAc hdet hdetc,
    variance_actual_cast A q hA hAc hdet hdetc]
  have hv : (rVariance A q:ℝ) ≠ 0 := by exact_mod_cast hvar.ne'
  simp only [absStudent, if_neg hv]
  apply congrArg ENNReal.ofReal
  rw [rScore_cast, Real.sqrt_div (sq_nonneg (rTau A q:ℝ)), Real.sqrt_sq_eq_abs]

lemma stat_order (A B : Finset (Fin 8)) (q : Fin 8 → ℚ)
    (ha : A.Nonempty) (hac : Aᶜ.Nonempty) (hb : B.Nonempty) (hbc : Bᶜ.Nonempty)
    (hda : (gram wxc A).det ≠ 0) (hdac : (gram wxc Aᶜ).det ≠ 0)
    (hdb : (gram wxc B).det ≠ 0) (hdbc : (gram wxc Bᶜ).det ≠ 0)
    (hva : 0 < rVariance A q) (hvb : 0 < rVariance B q) :
    (rScore A q < rScore B q) ↔
      (adjustedAR intervalWitnessPopulation (qreal q) A <
       adjustedAR intervalWitnessPopulation (qreal q) B) := by
  rw [stat_cast A q ha hac hda hdac hva, stat_cast B q hb hbc hdb hdbc hvb]
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)]
  have hsA : 0 ≤ (rScore A q:ℝ) := by rw [rScore_cast]; positivity
  rw [Real.sqrt_lt_sqrt_iff hsA]
  rw [rScore_cast, rScore_cast]
  norm_cast


end
end SAP.P002b.WH.W1.P.T26_L6
