import SAP.P001g.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W2.P.T121_L3

open Filter
open scoped BigOperators Topology

noncomputable section

lemma baseAtZero (y : Fin 3) : circleAffineW2 0 y = circleBaseW2 y := by
  fin_cases y <;> simp [circleAffineW2, circleBaseW2]

lemma sumOutcome {n : ℕ} (s : Fin n → Fin 3) (a : Fin 3 → ℝ) :
    (∑ i : Fin n, a (s i)) =
      ∑ y : Fin 3, (circleCountW2 s y : ℝ) * a y := by
  classical
  have h := (Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin 3)) s
    (fun i => a (s i))).symm
  have h' : (∑ i : Fin n, a (s i)) =
      ∑ y : Fin 3, ∑ i with s i = y, a (s i) := by simpa using h
  rw [h']
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_filter]
  calc
    (∑ i : Fin n, if s i = y then a (s i) else 0) =
        ∑ i : Fin n, if s i = y then a y else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with heq
      · rw [heq]
      · rfl
    _ = (circleCountW2 s y : ℝ) * a y := by
      rw [← Finset.sum_filter]
      simp [circleCountW2, Finset.sum_const]

lemma axis0Factor (y : Fin 3) :
    HasDerivAt (fun t : ℝ => circleAffineW2 (![t, 0] : Fin 2 → ℝ) y)
      (if y = 0 then (1 / 10 : ℝ) else if y = 1 then -(1 / 10 : ℝ) else 0) 0 := by
  fin_cases y
  · simpa [circleAffineW2] using (hasDerivAt_id (0 : ℝ)).div_const 10
  · convert (((hasDerivAt_id (0 : ℝ)).neg).div_const 10).const_add
      (Real.sqrt 2 / 4) using 1 <;> norm_num [circleAffineW2]
  · simpa [circleAffineW2] using (hasDerivAt_const (0 : ℝ) (1 : ℝ))

lemma axis1Factor (y : Fin 3) :
    HasDerivAt (fun t : ℝ => circleAffineW2 (![0, t] : Fin 2 → ℝ) y)
      (if y = 0 then 0 else if y = 1 then (1 / 10 : ℝ) else -(1 / 10 : ℝ)) 0 := by
  fin_cases y
  · simpa [circleAffineW2] using (hasDerivAt_const (0 : ℝ) (Real.sqrt 2 / 4))
  · simpa [circleAffineW2] using (hasDerivAt_id (0 : ℝ)).div_const 10
  · convert ((hasDerivAt_id (0 : ℝ)).div_const 10).const_sub
      (1 - Real.sqrt 2 / 2) using 1 <;> norm_num [circleAffineW2]


def axis0Slope (y : Fin 3) : ℝ :=
  if y = 0 then (1 / 10 : ℝ) else if y = 1 then -(1 / 10 : ℝ) else 0

def axis1Slope (y : Fin 3) : ℝ :=
  if y = 0 then 0 else if y = 1 then (1 / 10 : ℝ) else -(1 / 10 : ℝ)

lemma productScoreFactor {n : ℕ} (s : Fin n → Fin 3) (d : Fin n → ℝ) :
    (∑ i : Fin n, (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * d i) =
      circleDiscLikeW2 s 0 * ∑ i : Fin n, d i / circleBaseW2 (s i) := by
  classical
  have hdiv (i : Fin n) :
      (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) =
        circleDiscLikeW2 s 0 / circleBaseW2 (s i) := by
    apply (eq_div_iff (basePosW2 (s i)).ne').2
    simpa [circleDiscLikeW2, baseAtZero] using
      (Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
        (fun j => circleBaseW2 (s j)) (Finset.mem_univ i))
  calc
    (∑ i : Fin n, (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * d i) =
        ∑ i : Fin n, (circleDiscLikeW2 s 0 / circleBaseW2 (s i)) * d i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdiv]
    _ = ∑ i : Fin n, circleDiscLikeW2 s 0 * (d i / circleBaseW2 (s i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ = circleDiscLikeW2 s 0 * ∑ i : Fin n, d i / circleBaseW2 (s i) := by
      rw [Finset.mul_sum]

lemma axis0ProductDerivative {n : ℕ} (s : Fin n → Fin 3) :
    HasDerivAt (fun t : ℝ => circleDiscLikeW2 s (![t, 0] : Fin 2 → ℝ))
      (∑ i : Fin n,
        (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * axis0Slope (s i)) 0 := by
  classical
  have horigin : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
  simpa [circleDiscLikeW2, axis0Slope, baseAtZero, horigin, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ => axis0Factor (s i)))

lemma axis1ProductDerivative {n : ℕ} (s : Fin n → Fin 3) :
    HasDerivAt (fun t : ℝ => circleDiscLikeW2 s (![0, t] : Fin 2 → ℝ))
      (∑ i : Fin n,
        (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * axis1Slope (s i)) 0 := by
  classical
  have horigin : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
  simpa [circleDiscLikeW2, axis1Slope, baseAtZero, horigin, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ => axis1Factor (s i)))

lemma axis0ScoreSum {n : ℕ} (s : Fin n → Fin 3) :
    (∑ i : Fin n, axis0Slope (s i) / circleBaseW2 (s i)) =
      ((circleCountW2 s 0 : ℝ) / circleBaseW2 0 -
        (circleCountW2 s 1 : ℝ) / circleBaseW2 1) / 10 := by
  calc
    (∑ i : Fin n, axis0Slope (s i) / circleBaseW2 (s i)) =
        ∑ y : Fin 3, (circleCountW2 s y : ℝ) *
          (axis0Slope y / circleBaseW2 y) := sumOutcome s (fun y => axis0Slope y / circleBaseW2 y)
    _ = _ := by
      simp [Fin.sum_univ_succ, axis0Slope, circleBaseW2]
      ring

lemma axis1ScoreSum {n : ℕ} (s : Fin n → Fin 3) :
    (∑ i : Fin n, axis1Slope (s i) / circleBaseW2 (s i)) =
      ((circleCountW2 s 1 : ℝ) / circleBaseW2 1 -
        (circleCountW2 s 2 : ℝ) / circleBaseW2 2) / 10 := by
  calc
    (∑ i : Fin n, axis1Slope (s i) / circleBaseW2 (s i)) =
        ∑ y : Fin 3, (circleCountW2 s y : ℝ) *
          (axis1Slope y / circleBaseW2 y) := sumOutcome s (fun y => axis1Slope y / circleBaseW2 y)
    _ = _ := by
      simp [Fin.sum_univ_succ, axis1Slope, circleBaseW2]
      ring


end
end SAP.P001g.WH.W2.P.T121_L3

open SAP.P001g.WH.W2 SAP.P001g.WH.W2.P.T121_L3

theorem SAP.P001g.WH.W2.T121_L3_proof : SAP.P001g.WH.W2.T121_L3 := by
  intro n s
  constructor
  · have hprod := axis0ProductDerivative s
    have hcoef :
        (∑ i : Fin n,
          (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * axis0Slope (s i)) =
          circleDiscLikeW2 s 0 / 10 *
            ((circleCountW2 s 0 : ℝ) / circleBaseW2 0 -
              (circleCountW2 s 1 : ℝ) / circleBaseW2 1) := by
      calc
        _ = circleDiscLikeW2 s 0 *
            (∑ i : Fin n, axis0Slope (s i) / circleBaseW2 (s i)) :=
              productScoreFactor s (fun i => axis0Slope (s i))
        _ = _ := by rw [axis0ScoreSum]; ring
    simpa only [hcoef] using hprod
  · have hprod := axis1ProductDerivative s
    have hcoef :
        (∑ i : Fin n,
          (∏ j ∈ (Finset.univ.erase i), circleBaseW2 (s j)) * axis1Slope (s i)) =
          circleDiscLikeW2 s 0 / 10 *
            ((circleCountW2 s 1 : ℝ) / circleBaseW2 1 -
              (circleCountW2 s 2 : ℝ) / circleBaseW2 2) := by
      calc
        _ = circleDiscLikeW2 s 0 *
            (∑ i : Fin n, axis1Slope (s i) / circleBaseW2 (s i)) :=
              productScoreFactor s (fun i => axis1Slope (s i))
        _ = _ := by rw [axis1ScoreSum]; ring
    simpa only [hcoef] using hprod

