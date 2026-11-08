import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W2.P.T4_L3

open SAP.P002a
open scoped BigOperators ENNReal Matrix

def t012 : Finset (Fin 6) := insert 0 (insert 1 (insert 2 ∅))
def t013 : Finset (Fin 6) := insert 0 (insert 1 (insert 3 ∅))
def t014 : Finset (Fin 6) := insert 0 (insert 1 (insert 4 ∅))
def t015 : Finset (Fin 6) := insert 0 (insert 1 (insert 5 ∅))
def t023 : Finset (Fin 6) := insert 0 (insert 2 (insert 3 ∅))
def t024 : Finset (Fin 6) := insert 0 (insert 2 (insert 4 ∅))
def t025 : Finset (Fin 6) := insert 0 (insert 2 (insert 5 ∅))
def t034 : Finset (Fin 6) := insert 0 (insert 3 (insert 4 ∅))
def t035 : Finset (Fin 6) := insert 0 (insert 3 (insert 5 ∅))
def t045 : Finset (Fin 6) := insert 0 (insert 4 (insert 5 ∅))
def t123 : Finset (Fin 6) := insert 1 (insert 2 (insert 3 ∅))
def t124 : Finset (Fin 6) := insert 1 (insert 2 (insert 4 ∅))
def t125 : Finset (Fin 6) := insert 1 (insert 2 (insert 5 ∅))
def t134 : Finset (Fin 6) := insert 1 (insert 3 (insert 4 ∅))
def t135 : Finset (Fin 6) := insert 1 (insert 3 (insert 5 ∅))
def t145 : Finset (Fin 6) := insert 1 (insert 4 (insert 5 ∅))
def t234 : Finset (Fin 6) := insert 2 (insert 3 (insert 4 ∅))
def t235 : Finset (Fin 6) := insert 2 (insert 3 (insert 5 ∅))
def t245 : Finset (Fin 6) := insert 2 (insert 4 (insert 5 ∅))
def t345 : Finset (Fin 6) := insert 3 (insert 4 (insert 5 ∅))

def triples : Finset (Finset (Fin 6)) :=
  insert t012 (insert t013 (insert t014 (insert t015 (insert t023 (insert t024
    (insert t025 (insert t034 (insert t035 (insert t045 (insert t123 (insert t124
      (insert t125 (insert t134 (insert t135 (insert t145 (insert t234 (insert t235
        (insert t245 (insert t345 ∅)))))))))))))))))))

theorem assignments_eq : assignments W2Six.pop = triples := by decide

def gridQ (i : Fin 6) : ℚ :=
  match i.val with
  | 0 => -5/6
  | 1 => -1/2
  | 2 => -1/6
  | 3 => 1/6
  | 4 => 1/2
  | _ => 5/6

theorem gridX_eq_gridQ (i : Fin 6) : gridX i 0 = (gridQ i : ℝ) := by
  fin_cases i <;> norm_num [gridX, gridQ]

def responseQ (O : Finset (Fin 6)) (i : Fin 6) : ℚ :=
  if i ∈ O then 2 * gridQ i else gridQ i

theorem observedW_eq_responseQ (O : Finset (Fin 6)) (i : Fin 6) :
    observedW W2Six.pop (7/3) O i = (responseQ O i : ℝ) := by
  by_cases h : i ∈ O
  · simp [W2Six, observedW, observedY, observedD, binary, responseQ, h,
      gridX_eq_gridQ]
    <;> ring
  · simp [W2Six, observedW, observedY, observedD, binary, responseQ, h,
      gridX_eq_gridQ]

def meanQ (S : Finset (Fin 6)) (q : Fin 6 → ℚ) : ℚ :=
  (∑ i ∈ S, q i) / (S.card : ℚ)

def armInterceptQ (S O : Finset (Fin 6)) : ℚ :=
  let x : Fin 6 → ℚ := gridQ
  let q : Fin 6 → ℚ := responseQ O
  meanQ S q -
    ((meanQ S (fun i => x i * q i) - meanQ S x * meanQ S q) /
      (meanQ S (fun i => x i ^ 2) - (meanQ S x) ^ 2)) * meanQ S x

noncomputable def meanR (S : Finset (Fin 6)) (q : Fin 6 → ℝ) : ℝ := groupMean S q

noncomputable def armSlopeR (S : Finset (Fin 6)) (q : Fin 6 → ℝ) : ℝ :=
  (meanR S (fun i => gridX i 0 * q i) - meanR S (fun i => gridX i 0) * meanR S q) /
    (meanR S (fun i => (gridX i 0) ^ 2) - (meanR S (fun i => gridX i 0)) ^ 2)

noncomputable def armInterceptR (S : Finset (Fin 6)) (q : Fin 6 → ℝ) : ℝ :=
  meanR S q - armSlopeR S q * meanR S (fun i => gridX i 0)

theorem groupMean_castQ (S : Finset (Fin 6)) (q : Fin 6 → ℚ) :
    groupMean S (fun i => (q i : ℝ)) = (meanQ S q : ℝ) := by
  unfold groupMean meanQ
  rw [← Rat.cast_sum, Rat.cast_div]
  norm_cast

theorem armInterceptR_eq_Q (S O : Finset (Fin 6)) :
    armInterceptR S (observedW W2Six.pop (7/3) O) = (armInterceptQ S O : ℝ) := by
  rw [show observedW W2Six.pop (7/3) O = fun i => (responseQ O i : ℝ) from by
    funext i; exact observedW_eq_responseQ O i]
  have hx : meanR S (fun i => gridX i 0) = (meanQ S gridQ : ℝ) := by
    rw [meanR, show (fun i : Fin 6 => gridX i 0) = fun i => (gridQ i : ℝ) from by
      funext i; exact gridX_eq_gridQ i]
    exact groupMean_castQ S gridQ
  have hq : meanR S (fun i => (responseQ O i : ℝ)) =
      (meanQ S (responseQ O) : ℝ) := by
    exact groupMean_castQ S (responseQ O)
  have hxq : meanR S (fun i => gridX i 0 * (responseQ O i : ℝ)) =
      (meanQ S (fun i => gridQ i * responseQ O i) : ℝ) := by
    rw [meanR, show (fun i : Fin 6 => gridX i 0 * (responseQ O i : ℝ)) =
      fun i => ((gridQ i * responseQ O i : ℚ) : ℝ) from by
        funext i; rw [gridX_eq_gridQ]; norm_cast]
    exact groupMean_castQ S (fun i => gridQ i * responseQ O i)
  have hx2 : meanR S (fun i => (gridX i 0)^2) =
      (meanQ S (fun i => gridQ i^2) : ℝ) := by
    rw [meanR, show (fun i : Fin 6 => (gridX i 0)^2) =
      fun i => ((gridQ i^2 : ℚ) : ℝ) from by
        funext i; rw [gridX_eq_gridQ]; norm_cast]
    exact groupMean_castQ S (fun i => gridQ i^2)
  simp only [armInterceptR, armSlopeR, armInterceptQ, hx, hq, hxq, hx2]
  push_cast
  ring

theorem det_gram_formula (S : Finset (Fin 6)) (hS : S.card = 3) :
    (gram gridX S).det =
      groupMean S (fun i => (gridX i 0)^2) - (groupMean S (fun i => gridX i 0))^2 := by
  let e : Option (Fin 1) ≃ Fin 2 := (finSuccEquiv 1).symm
  have he0 : (finSuccEquiv 1) (0 : Fin 2) = none := finSuccEquiv_zero
  have he1 : (finSuccEquiv 1) (1 : Fin 2) = some 0 := by
    simpa using finSuccEquiv_succ (0 : Fin 1)
  have hm : (gram gridX S).reindex e e =
      !![1, groupMean S (fun i => gridX i 0); groupMean S (fun i => gridX i 0),
        groupMean S (fun i => (gridX i 0)^2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, he0, he1, Matrix.reindex_apply, gram, augmented, groupMean, hS, pow_two]
  rw [← Matrix.det_reindex_self e (gram gridX S), hm, Matrix.det_fin_two_of]
  ring

theorem det_ne_zero_of_mem (S : Finset (Fin 6)) (hS : S ∈ triples) :
    (gram gridX S).det ≠ 0 := by
  have hc : S.card = 3 := by
    rw [← assignments_eq] at hS
    simp only [assignments, W2Six, Finset.mem_powersetCard] at hS
    exact hS.2
  rw [det_gram_formula S hc]
  simp [triples] at hS
  rcases hS with hS | hS | hS | hS | hS | hS | hS | hS | hS | hS |
      hS | hS | hS | hS | hS | hS | hS | hS | hS | hS
  all_goals subst S
  all_goals norm_num [t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    groupMean, gridX, Finset.sum_insert]

theorem card_eq_three_of_mem (S : Finset (Fin 6)) (hS : S ∈ triples) : S.card = 3 := by
  rw [← assignments_eq] at hS
  simp only [assignments, W2Six, Finset.mem_powersetCard] at hS
  exact hS.2

theorem compl_mem_triples (S : Finset (Fin 6)) (hS : S ∈ triples) : Sᶜ ∈ triples := by
  have hc : Sᶜ.card = 3 := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin, card_eq_three_of_mem S hS]
  have hm : Sᶜ ∈ assignments W2Six.pop := by
    simp [assignments, W2Six, Finset.mem_powersetCard, hc]
  rw [assignments_eq] at hm
  exact hm

theorem groupMean_residual (S : Finset (Fin 6)) (q : Fin 6 → ℝ) (b : ℝ)
    (hcard : S.card = 3) :
    groupMean S (fun i => q i - gridX i 0 * b) =
      groupMean S q - b * groupMean S (fun i => gridX i 0) := by
  unfold groupMean
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hcard]
  ring

theorem armIntercept_fit (S : Finset (Fin 6)) (q : Fin 6 → ℝ)
    (hcard : S.card = 3) (hdet : (gram gridX S).det ≠ 0) :
    fitted W2Six q S true =
      fun a => if a = none then armInterceptR S q else
        if a = some 0 then
          (meanR S (fun i => gridX i 0 * q i) -
            meanR S (fun i => gridX i 0) * meanR S q) /
            (meanR S (fun i => (gridX i 0)^2) - (meanR S (fun i => gridX i 0))^2)
        else 0 := by
  let mx := meanR S (fun i => gridX i 0)
  let mq := meanR S q
  let mx2 := meanR S (fun i => (gridX i 0)^2)
  let mxq := meanR S (fun i => gridX i 0 * q i)
  let d := mx2 - mx^2
  let b := (mxq - mx * mq) / d
  let a := mq - b * mx
  let c : Option (Fin 1) → ℝ := fun j => if j = none then a else if j = some 0 then b else 0
  have hc0 : c none = a := by simp [c]
  have hc1 : c (some 0) = b := by simp [c]
  have hd : d ≠ 0 := by
    dsimp [d, mx, mx2, meanR]
    rw [← det_gram_formula S hcard]
    exact hdet
  have hg00 : gram gridX S none none = 1 := by
    simp [gram, augmented, groupMean, hcard]
  have hg01 : gram gridX S none (some 0) = mx := by
    simp [gram, augmented, mx, meanR]
  have hg10 : gram gridX S (some 0) none = mx := by
    simp [gram, augmented, mx, meanR]
  have hg11 : gram gridX S (some 0) (some 0) = mx2 := by
    simp [gram, augmented, mx2, meanR, pow_two]
  have hs0 : score gridX S q none = mq := by
    simp [score, augmented, mq, meanR]
  have hs1 : score gridX S q (some 0) = mxq := by
    simp [score, augmented, mxq, meanR]
  have heq0 : mq = a + mx * b := by
    dsimp [a]
    ring
  have hb : d * b = mxq - mx * mq := by
    dsimp only [b]
    field_simp [hd]
  have heq1 : mxq = mx * a + mx2 * b := by
    calc
      mxq = mx * mq + d * b := by rw [hb]; ring
      _ = mx * a + mx2 * b := by dsimp [d, a]; ring
  have hsolve : score gridX S q = (gram gridX S).mulVec c := by
    ext j
    cases j with
    | none =>
      rw [hs0, Matrix.mulVec_apply_eq_sum, Fintype.sum_option, Fin.sum_univ_succ]
      simp only [Fin.sum_univ_zero]
      rw [hg00, hg01, hc0, hc1]
      simpa using heq0
    | some j =>
      fin_cases j
      change score gridX S q (some 0) = (gram gridX S).mulVec c (some 0)
      rw [hs1, Matrix.mulVec_apply_eq_sum, Fintype.sum_option, Fin.sum_univ_succ]
      simp only [Fin.sum_univ_zero]
      rw [hg10, hg11, hc0, hc1]
      simpa using heq1
  have hi : IsUnit (gram gridX S).det := isUnit_iff_ne_zero.mpr hdet
  have hfit : fitted W2Six q S true = c := by
    unfold fitted
    change ols gridX S q = c
    unfold ols
    rw [if_pos hdet]
    calc
      (gram gridX S)⁻¹.mulVec (score gridX S q) =
          (gram gridX S)⁻¹.mulVec ((gram gridX S).mulVec c) := by rw [hsolve]
      _ = c := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hi, Matrix.one_mulVec]
  funext j
  cases j with
  | none => simpa [c, a, b, d, mx, mq, mx2, mxq, armInterceptR, armSlopeR, meanR] using
      congrFun hfit none
  | some j =>
      fin_cases j
      simpa [c, b, d, mx, mq, mx2, mxq, armSlopeR, meanR] using congrFun hfit (some 0)

theorem adjustedTau_eq_armInterceptQ (O S : Finset (Fin 6))
    (hS : S ∈ triples) (hSc : Sᶜ ∈ triples) :
    adjustedTau W2Six (observedW W2Six.pop (7/3) O) S =
      (armInterceptQ S O : ℝ) - (armInterceptQ Sᶜ O : ℝ) := by
  let q := observedW W2Six.pop (7/3) O
  have hcS := card_eq_three_of_mem S hS
  have hcC := card_eq_three_of_mem Sᶜ hSc
  have hdS := det_ne_zero_of_mem S hS
  have hdC := det_ne_zero_of_mem Sᶜ hSc
  have hfS := armIntercept_fit S q hcS hdS
  have hfC := armIntercept_fit Sᶜ q hcC hdC
  have hfC' : fitted W2Six q S false =
      fun a => if a = none then armInterceptR Sᶜ q else
        if a = some 0 then armSlopeR Sᶜ q else 0 := by
    simpa [fitted, armSlopeR, meanR] using hfC
  have hsS : (fitted W2Six q S true) (some 0) = armSlopeR S q := by
    rw [hfS]
    simp [armSlopeR, meanR]
  have hsC : (fitted W2Six q S false) (some 0) = armSlopeR Sᶜ q := by
    rw [hfC']
    simp [armSlopeR, meanR]
  have hsS' : (fitted W2Six (observedW W2Six.pop (7/3) O) S true) (some 0) =
      armSlopeR S (observedW W2Six.pop (7/3) O) := by simpa [q] using hsS
  have hsC' : (fitted W2Six (observedW W2Six.pop (7/3) O) S false) (some 0) =
      armSlopeR Sᶜ (observedW W2Six.pop (7/3) O) := by simpa [q] using hsC
  have hx : W2Six.x = gridX := rfl
  unfold adjustedTau adjustedWith
  simp only [slopeDot, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [hx]
  rw [hsS', hsC']
  simp only [add_zero]
  rw [groupMean_residual S (observedW W2Six.pop (7/3) O)
    (armSlopeR S (observedW W2Six.pop (7/3) O)) hcS]
  rw [groupMean_residual Sᶜ (observedW W2Six.pop (7/3) O)
    (armSlopeR Sᶜ (observedW W2Six.pop (7/3) O)) hcC]
  change armInterceptR S (observedW W2Six.pop (7/3) O) -
      armInterceptR Sᶜ (observedW W2Six.pop (7/3) O) = _
  rw [armInterceptR_eq_Q S O, armInterceptR_eq_Q Sᶜ O]

def tauQ (O S : Finset (Fin 6)) : ℚ := armInterceptQ S O - armInterceptQ Sᶜ O

def armInterceptFastQ (S O : Finset (Fin 6)) : ℚ :=
  let X := ∑ i ∈ S, gridQ i
  let Q := ∑ i ∈ S, responseQ O i
  let X2 := ∑ i ∈ S, gridQ i^2
  let XQ := ∑ i ∈ S, gridQ i * responseQ O i
  (Q * X2 - X * XQ) / (3 * X2 - X^2)

def tauFastQ (O S : Finset (Fin 6)) : ℚ :=
  armInterceptFastQ S O - armInterceptFastQ Sᶜ O


theorem intercept_algebra (X Q X2 XQ : ℚ) (hD : 3 * X2 - X^2 ≠ 0) :
    Q/3 - ((XQ/3 - (X/3)*(Q/3))/(X2/3-(X/3)^2))*(X/3) =
      (Q*X2-X*XQ)/(3*X2-X^2) := by
  field_simp [hD]
  <;> ring

theorem armInterceptQ_eq_fast (S O : Finset (Fin 6)) (hS : S ∈ triples) :
    armInterceptQ S O = armInterceptFastQ S O := by
  have hc := card_eq_three_of_mem S hS
  let X := ∑ i ∈ S, gridQ i
  let Q := ∑ i ∈ S, responseQ O i
  let X2 := ∑ i ∈ S, gridQ i^2
  let XQ := ∑ i ∈ S, gridQ i * responseQ O i
  have hD : 3 * X2 - X^2 ≠ 0 := by
    simp [triples] at hS
    rcases hS with hS | hS | hS | hS | hS | hS | hS | hS | hS | hS |
      hS | hS | hS | hS | hS | hS | hS | hS | hS | hS
    all_goals subst S
    all_goals norm_num [X, X2, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
      t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
      Finset.sum_insert]
  have hmeanQ : meanQ S (responseQ O) = Q/3 := by simp [meanQ, Q, hc]
  have hmeanX : meanQ S gridQ = X/3 := by simp [meanQ, X, hc]
  have hmeanX2 : meanQ S (fun i => gridQ i^2) = X2/3 := by simp [meanQ, X2, hc]
  have hmeanXQ : meanQ S (fun i => gridQ i * responseQ O i) = XQ/3 := by
    simp [meanQ, XQ, hc]
  unfold armInterceptQ armInterceptFastQ
  simp only [hmeanQ, hmeanX, hmeanX2, hmeanXQ]
  exact intercept_algebra X Q X2 XQ hD

def tripleAt (i : Fin 20) : Finset (Fin 6) :=
  match i.val with
  | 0 => t012
  | 1 => t013
  | 2 => t014
  | 3 => t015
  | 4 => t023
  | 5 => t024
  | 6 => t025
  | 7 => t034
  | 8 => t035
  | 9 => t045
  | 10 => t123
  | 11 => t124
  | 12 => t125
  | 13 => t134
  | 14 => t135
  | 15 => t145
  | 16 => t234
  | 17 => t235
  | 18 => t245
  | _ => t345

def tripleCompAt (i : Fin 20) : Finset (Fin 6) :=
  match i.val with
  | 0 => t345
  | 1 => t245
  | 2 => t235
  | 3 => t234
  | 4 => t145
  | 5 => t135
  | 6 => t134
  | 7 => t125
  | 8 => t124
  | 9 => t123
  | 10 => t045
  | 11 => t035
  | 12 => t034
  | 13 => t025
  | 14 => t024
  | 15 => t023
  | 16 => t015
  | 17 => t014
  | 18 => t013
  | _ => t012

theorem tripleCompAt_eq_compl (i : Fin 20) : tripleCompAt i = (tripleAt i)ᶜ := by
  fin_cases i <;> decide

def tauIndexedFastQ (i j : Fin 20) : ℚ :=
  armInterceptFastQ (tripleAt j) (tripleAt i) -
    armInterceptFastQ (tripleCompAt j) (tripleAt i)

theorem tripleAt_image : Finset.univ.image tripleAt = triples := by decide

theorem tripleAt_injective : Function.Injective tripleAt := by decide

def pairAt (ij : Fin 20 × Fin 20) : Finset (Fin 6) × Finset (Fin 6) :=
  (tripleAt ij.1, tripleAt ij.2)

theorem pairAt_injective : Function.Injective pairAt := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h1 : tripleAt i = tripleAt i' := congrArg Prod.fst h
  have h2 : tripleAt j = tripleAt j' := congrArg Prod.snd h
  exact Prod.ext (tripleAt_injective h1) (tripleAt_injective h2)

theorem triple_product_eq_index_image :
    triples.product triples =
      (Finset.univ.product Finset.univ).image pairAt := by
  rw [← tripleAt_image]
  change (Finset.univ.image tripleAt).product (Finset.univ.image tripleAt) =
    (Finset.univ.product Finset.univ).image (Prod.map tripleAt tripleAt)
  exact (Finset.prodMap_image_product tripleAt tripleAt Finset.univ Finset.univ).symm

theorem row_count_0 :
    (∑ j : Fin 20, if tauIndexedFastQ (0 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_1 :
    (∑ j : Fin 20, if tauIndexedFastQ (1 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_2 :
    (∑ j : Fin 20, if tauIndexedFastQ (2 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_3 :
    (∑ j : Fin 20, if tauIndexedFastQ (3 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_4 :
    (∑ j : Fin 20, if tauIndexedFastQ (4 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_5 :
    (∑ j : Fin 20, if tauIndexedFastQ (5 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_6 :
    (∑ j : Fin 20, if tauIndexedFastQ (6 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_7 :
    (∑ j : Fin 20, if tauIndexedFastQ (7 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_8 :
    (∑ j : Fin 20, if tauIndexedFastQ (8 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_9 :
    (∑ j : Fin 20, if tauIndexedFastQ (9 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_10 :
    (∑ j : Fin 20, if tauIndexedFastQ (10 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_11 :
    (∑ j : Fin 20, if tauIndexedFastQ (11 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_12 :
    (∑ j : Fin 20, if tauIndexedFastQ (12 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_13 :
    (∑ j : Fin 20, if tauIndexedFastQ (13 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_14 :
    (∑ j : Fin 20, if tauIndexedFastQ (14 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_15 :
    (∑ j : Fin 20, if tauIndexedFastQ (15 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_16 :
    (∑ j : Fin 20, if tauIndexedFastQ (16 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_17 :
    (∑ j : Fin 20, if tauIndexedFastQ (17 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 18 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_18 :
    (∑ j : Fin 20, if tauIndexedFastQ (18 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

theorem row_count_19 :
    (∑ j : Fin 20, if tauIndexedFastQ (19 : Fin 20) j ≠ 0 then (1 : ℕ) else 0) = 12 := by
  norm_num [Fin.sum_univ_succ, tauIndexedFastQ, armInterceptFastQ, tripleAt, tripleCompAt, responseQ, gridQ, t012, t013, t014, t015, t023, t024, t025, t034,
    t035, t045, t123, t124, t125, t134, t135, t145, t234, t235, t245, t345,
    Finset.sum_insert]

def rowExpected (i : Fin 20) : ℕ :=
  match i.val with
  | 0 => 12 | 1 => 12 | 2 => 18 | 3 => 18 | 4 => 18
  | 5 => 12 | 6 => 18 | 7 => 12 | 8 => 18 | 9 => 18
  | 10 => 18 | 11 => 18 | 12 => 12 | 13 => 18 | 14 => 12
  | 15 => 18 | 16 => 18 | 17 => 18 | 18 => 12 | _ => 12

theorem indexed_count :
    (∑ i : Fin 20, ∑ j : Fin 20,
      if tauIndexedFastQ i j ≠ 0 then (1 : ℕ) else 0) = 312 := by
  have hrows : ∀ i : Fin 20,
      (∑ j : Fin 20, if tauIndexedFastQ i j ≠ 0 then (1 : ℕ) else 0) = rowExpected i := by
    intro i
    fin_cases i
    all_goals
      first
      | simpa [rowExpected] using row_count_0
      | simpa [rowExpected] using row_count_1
      | simpa [rowExpected] using row_count_2
      | simpa [rowExpected] using row_count_3
      | simpa [rowExpected] using row_count_4
      | simpa [rowExpected] using row_count_5
      | simpa [rowExpected] using row_count_6
      | simpa [rowExpected] using row_count_7
      | simpa [rowExpected] using row_count_8
      | simpa [rowExpected] using row_count_9
      | simpa [rowExpected] using row_count_10
      | simpa [rowExpected] using row_count_11
      | simpa [rowExpected] using row_count_12
      | simpa [rowExpected] using row_count_13
      | simpa [rowExpected] using row_count_14
      | simpa [rowExpected] using row_count_15
      | simpa [rowExpected] using row_count_16
      | simpa [rowExpected] using row_count_17
      | simpa [rowExpected] using row_count_18
      | simpa [rowExpected] using row_count_19
  calc
    (∑ i : Fin 20, ∑ j : Fin 20,
        if tauIndexedFastQ i j ≠ 0 then (1 : ℕ) else 0) =
      ∑ i : Fin 20, rowExpected i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrows i
    _ = 312 := by norm_num [Fin.sum_univ_succ, rowExpected]

theorem adjustedTau_eq_tauQ (O S : Finset (Fin 6))
    (hS : S ∈ triples) (hSc : Sᶜ ∈ triples) :
    adjustedTau W2Six (observedW W2Six.pop (7/3) O) S = (tauQ O S : ℝ) := by
  rw [adjustedTau_eq_armInterceptQ O S hS hSc]
  simp [tauQ, Rat.cast_sub]

theorem adjustedTau_eq_tauFastQ (O S : Finset (Fin 6))
    (hS : S ∈ triples) (hSc : Sᶜ ∈ triples) :
    adjustedTau W2Six (observedW W2Six.pop (7/3) O) S = (tauFastQ O S : ℝ) := by
  rw [adjustedTau_eq_armInterceptQ O S hS hSc]
  rw [armInterceptQ_eq_fast S O hS, armInterceptQ_eq_fast Sᶜ O hSc]
  simp [tauFastQ, Rat.cast_sub]

theorem sigma_nonneg (O S : Finset (Fin 6)) (hS : S ∈ triples) :
    0 ≤ adjustedSigma2 W2Six (observedW W2Six.pop (7/3) O) S := by
  have hcS := card_eq_three_of_mem S hS
  have hSc := card_eq_three_of_mem Sᶜ (compl_mem_triples S hS)
  unfold adjustedSigma2 rss
  simp only [W2Six, controlSize, hcS, hSc]
  positivity

theorem absStudent_ne_zero_iff (t s : ℝ) (hs : 0 ≤ s) :
    absStudent t s ≠ 0 ↔ t ≠ 0 := by
  unfold absStudent
  by_cases hz : s = 0
  · simp [hz]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    simp only [if_neg hz]
    constructor
    · intro h ht
      subst t
      apply h
      simp
    · intro ht h
      have hle : |t| / Real.sqrt s ≤ 0 := ENNReal.ofReal_eq_zero.mp h
      have hpos : 0 < |t| / Real.sqrt s := div_pos (abs_pos.mpr ht) hr
      linarith

theorem adjustedAR_ne_zero_iff_tauQ (O S : Finset (Fin 6))
    (hS : S ∈ triples) :
    adjustedAR W2Six (observedW W2Six.pop (7/3) O) S ≠ 0 ↔ tauFastQ O S ≠ 0 := by
  have hSc := compl_mem_triples S hS
  change absStudent (adjustedTau W2Six (observedW W2Six.pop (7/3) O) S)
    (adjustedSigma2 W2Six (observedW W2Six.pop (7/3) O) S) ≠ 0 ↔ _
  rw [absStudent_ne_zero_iff _ _ (sigma_nonneg O S hS)]
  rw [adjustedTau_eq_tauFastQ O S hS hSc]
  constructor
  · intro h hn
    apply h
    exact_mod_cast hn
  · intro h hn
    apply h
    exact_mod_cast hn

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem rational_count :
    ((triples.product triples).filter fun OT => tauFastQ OT.1 OT.2 ≠ 0).card = 312 := by
  have hfilter :
      (triples.product triples).filter (fun OT => tauFastQ OT.1 OT.2 ≠ 0) =
        ((Finset.univ.product Finset.univ).filter
          (fun ij => tauFastQ (tripleAt ij.1) (tripleAt ij.2) ≠ 0)).image pairAt := by
    rw [triple_product_eq_index_image]
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨ij, hij, hp⟩, hstat⟩
      subst p
      exact ⟨ij, ⟨hij, hstat⟩, rfl⟩
    · rintro ⟨ij, ⟨hij, hstat⟩, rfl⟩
      exact ⟨⟨ij, hij, rfl⟩, hstat⟩
  rw [hfilter, Finset.card_image_iff.mpr (pairAt_injective.injOn), Finset.card_filter]
  change (∑ ij ∈ Finset.univ ×ˢ Finset.univ,
    if tauFastQ (tripleAt ij.1) (tripleAt ij.2) ≠ 0 then (1 : ℕ) else 0) = 312
  rw [Finset.sum_product]
  have heq : ∀ i j : Fin 20,
      (tauFastQ (tripleAt i) (tripleAt j) ≠ 0) ↔ tauIndexedFastQ i j ≠ 0 := by
    intro i j
    simp [tauFastQ, tauIndexedFastQ, tripleCompAt_eq_compl]
  simp_rw [heq]
  exact indexed_count

theorem filter_eq_rational :
    (((assignments W2Six.pop).product (assignments W2Six.pop)).filter fun OT =>
      adjustedAR W2Six (observedW W2Six.pop (7/3) OT.1) OT.2 ≠ 0) =
    ((triples.product triples).filter fun OT => tauFastQ OT.1 OT.2 ≠ 0) := by
  rw [assignments_eq]
  ext p
  rcases p with ⟨O, S⟩
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hprod, hstat⟩
    rcases Finset.mem_product.mp hprod with ⟨hO, hS⟩
    exact ⟨Finset.mem_product.mpr ⟨hO, hS⟩,
      (adjustedAR_ne_zero_iff_tauQ O S hS).mp hstat⟩
  · rintro ⟨hprod, hstat⟩
    rcases Finset.mem_product.mp hprod with ⟨hO, hS⟩
    exact ⟨Finset.mem_product.mpr ⟨hO, hS⟩,
      (adjustedAR_ne_zero_iff_tauQ O S hS).mpr hstat⟩

end SAP.P002a.WH.W2.P.T4_L3

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem SAP.P002a.WH.W2.T4_L3_proof : SAP.P002a.WH.W2.T4_L3 := by
  unfold SAP.P002a.WH.W2.T4_L3
  change Finset.card (((assignments W2Six.pop).product (assignments W2Six.pop)).filter
    (fun OT => adjustedAR W2Six (observedW W2Six.pop (7/3) OT.1) OT.2 ≠ 0)) = 312
  calc
    Finset.card (((assignments W2Six.pop).product (assignments W2Six.pop)).filter
        (fun OT => adjustedAR W2Six (observedW W2Six.pop (7/3) OT.1) OT.2 ≠ 0)) =
      Finset.card ((SAP.P002a.WH.W2.P.T4_L3.triples.product
        SAP.P002a.WH.W2.P.T4_L3.triples).filter
          (fun OT => SAP.P002a.WH.W2.P.T4_L3.tauFastQ OT.1 OT.2 ≠ 0)) :=
        congrArg Finset.card SAP.P002a.WH.W2.P.T4_L3.filter_eq_rational
    _ = 312 := SAP.P002a.WH.W2.P.T4_L3.rational_count
