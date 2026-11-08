import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Classical

namespace SAP.P037a.WH.W1.P.T1_L3

open SAP.P037a

private noncomputable def residual {B : ℕ} (w : Fin B → CompositionAssignment)
    (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ) (p : Fin B × Fin 4) : ℝ :=
  observedOutcome (w p.1) p.2 - alpha p.1 -
    ∑ k : Fin 3, regressionColumns (w p.1) k p.2 * theta k

private theorem loss_eq_sum_residual {B : ℕ} (w : Fin B → CompositionAssignment)
    (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ) :
    blockRegressionLoss w alpha theta = ∑ p : Fin B × Fin 4, residual w alpha theta p ^ 2 := by
  simp [blockRegressionLoss, residual, Fintype.sum_prod_type]

private theorem finite_quadratic_minimum {ι : Type} [Fintype ι] [DecidableEq ι]
    (r x : ι → ℝ)
    (hmin : ∀ t : ℝ, (∑ i, (r i - t * x i) ^ 2) ≥ ∑ i, r i ^ 2) :
    ∑ i, x i * r i = 0 := by
  let s : ℝ := ∑ i, x i * r i
  let q : ℝ := ∑ i, x i ^ 2
  have hexpand (t : ℝ) :
      (∑ i, (r i - t * x i) ^ 2) = (∑ i, r i ^ 2) - 2*t*s + t^2*q := by
    dsimp [s, q]
    simp_rw [sub_sq]
    calc
      _ = (∑ i, r i ^ 2) - (∑ i, 2 * r i * (t * x i)) +
          ∑ i, (t * x i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ i, r i ^ 2) - 2*t*s + t^2*q := by
        have hmid : (∑ i, 2 * r i * (t * x i)) = 2*t*s := by
          calc
            _ = ∑ i, (2*t) * (x i * r i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (2*t) * s := by rw [Finset.mul_sum]
        have hpow : (∑ i, (t * x i) ^ 2) = t^2*q := by
          calc
            _ = ∑ i, t^2 * x i^2 := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = t^2 * q := by rw [Finset.mul_sum]
        rw [hmid, hpow]
  have ht := hmin (s / (q + 1))
  rw [hexpand] at ht
  have hq : 0 ≤ q := by
    dsimp [q]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hden : 0 < q + 1 := by linarith
  have hs : s = 0 := by
    by_contra hn
    have hs2 : 0 < s^2 := sq_pos_of_ne_zero hn
    have : (∑ i, r i ^ 2) - 2 * (s / (q + 1)) * s +
        (s / (q + 1)) ^ 2 * q < ∑ i, r i ^ 2 := by
      have hfactor :
          -2 * (s / (q + 1)) * s + (s / (q + 1)) ^ 2 * q =
            -(s^2 * (q + 2) / (q + 1)^2) := by
        field_simp
        ring
      calc
        _ = (∑ i, r i ^ 2) - (s^2 * (q + 2) / (q + 1)^2) := by
          calc
            _ = (∑ i, r i ^ 2) + (-2 * (s / (q + 1)) * s +
                (s / (q + 1)) ^ 2 * q) := by ring
            _ = _ := by rw [hfactor]; ring
        _ < _ := by
          have hpos : 0 < s^2 * (q + 2) / (q + 1)^2 := by
            apply div_pos
            · exact mul_pos hs2 (by linarith)
            · positivity
          linarith
    linarith
  simpa [s] using hs

private theorem centeredCross_add (x y z : Fin 4 → ℝ) :
    centeredCross x (fun i => y i + z i) = centeredCross x y + centeredCross x z := by
  unfold centeredCross
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

private theorem centeredCross_mul (x y : Fin 4 → ℝ) (c : ℝ) :
    centeredCross x (fun i => c * y i) = c * centeredCross x y := by
  unfold centeredCross
  have h1 : (∑ i, x i * (c * y i)) = c * ∑ i, x i * y i := by
    calc
      _ = ∑ i, c * (x i * y i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i, x i * y i := by rw [Finset.mul_sum]
  have h2 : (∑ i, c * y i) = c * ∑ i, y i := by rw [← Finset.mul_sum]
  rw [h1, h2]
  ring

private theorem centeredCross_sum {κ : Type} [Fintype κ]
    (x : Fin 4 → ℝ) (y : κ → Fin 4 → ℝ) :
    centeredCross x (fun i => ∑ k, y k i) = ∑ k, centeredCross x (y k) := by
  unfold centeredCross
  have h1 : (∑ i : Fin 4, x i * ∑ k, y k i) = ∑ k, ∑ i, x i * y k i := by
    calc
      _ = ∑ i, ∑ k, x i * y k i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ k, ∑ i, x i * y k i := Finset.sum_comm
  have h2 : (∑ i : Fin 4, ∑ k, y k i) = ∑ k, ∑ i, y k i := by rw [Finset.sum_comm]
  have h3 : ((∑ i : Fin 4, x i) * (∑ k, ∑ i, y k i)) / 4 =
      ∑ k, ((∑ i : Fin 4, x i) * (∑ i, y k i)) / 4 := by
    calc
      _ = (∑ k, (∑ i : Fin 4, x i) * (∑ i, y k i)) / 4 := by rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_div]
  rw [h1, h2, h3]
  rw [Finset.sum_sub_distrib]

private theorem centeredCross_const (x : Fin 4 → ℝ) (c : ℝ) :
    centeredCross x (fun _ : Fin 4 => c) = 0 := by
  unfold centeredCross
  simp only [Fin.sum_univ_four]
  ring

end SAP.P037a.WH.W1.P.T1_L3

theorem SAP.P037a.WH.W1.T1_L3_proof : SAP.P037a.WH.W1.T1_L3 := by
  intro B w alpha theta hOLS
  let r : Fin B × Fin 4 → ℝ :=
    SAP.P037a.WH.W1.P.T1_L3.residual w alpha theta
  have hloss := SAP.P037a.WH.W1.P.T1_L3.loss_eq_sum_residual w alpha theta
  have hmin_intercept (b : Fin B) (t : ℝ) :
      (∑ p : Fin B × Fin 4, (r p - t * (if p.1 = b then (1:ℝ) else 0)) ^ 2) ≥ ∑ p, r p ^ 2 := by
    let alpha' : Fin B → ℝ := fun b' => if b' = b then alpha b' + t else alpha b'
    have hm := hOLS alpha' theta
    rw [hloss, SAP.P037a.WH.W1.P.T1_L3.loss_eq_sum_residual] at hm
    have hpoint : ∀ p : Fin B × Fin 4,
        SAP.P037a.WH.W1.P.T1_L3.residual w alpha' theta p =
          r p - t * (if p.1 = b then (1:ℝ) else 0) := by
      intro p
      dsimp [r, SAP.P037a.WH.W1.P.T1_L3.residual, alpha']
      split_ifs <;> ring
    simp_rw [hpoint] at hm
    exact hm
  have hinter (b : Fin B) : ∑ i : Fin 4, r (b,i) = 0 := by
    have h := SAP.P037a.WH.W1.P.T1_L3.finite_quadratic_minimum
      (fun p : Fin B × Fin 4 => r p)
      (fun p => if p.1 = b then (1:ℝ) else 0) (hmin_intercept b)
    have heval : (∑ p : Fin B × Fin 4, (if p.1 = b then (1:ℝ) else 0) * r p) =
        ∑ i : Fin 4, r (b,i) := by
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_ite_eq']
    rw [heval] at h
    exact h
  have hmin_slope (k : Fin 3) (t : ℝ) :
      (∑ p : Fin B × Fin 4,
        (r p - t * regressionColumns (w p.1) k p.2)^2) ≥ ∑ p, r p^2 := by
    let theta' : Fin 3 → ℝ := fun l => if l = k then theta l + t else theta l
    have hm := hOLS alpha theta'
    rw [hloss, SAP.P037a.WH.W1.P.T1_L3.loss_eq_sum_residual] at hm
    have hpoint : ∀ p : Fin B × Fin 4,
        SAP.P037a.WH.W1.P.T1_L3.residual w alpha theta' p =
          r p - t * regressionColumns (w p.1) k p.2 := by
      intro p
      dsimp [r, SAP.P037a.WH.W1.P.T1_L3.residual, theta']
      have hpred : (∑ l : Fin 3, regressionColumns (w p.1) l p.2 *
          (if l = k then theta l + t else theta l)) =
          (∑ l : Fin 3, regressionColumns (w p.1) l p.2 * theta l) +
            t * regressionColumns (w p.1) k p.2 := by
        calc
          _ = ∑ l : Fin 3, (regressionColumns (w p.1) l p.2 * theta l +
              if l = k then regressionColumns (w p.1) l p.2 * t else 0) := by
            apply Finset.sum_congr rfl
            intro l hl
            by_cases hkl : l = k
            · subst l
              simp
              ring
            · simp [hkl]
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp [Finset.sum_ite_eq', mul_comm]
      rw [hpred]
      ring
    simp_rw [hpoint] at hm
    exact hm
  have hslope (k : Fin 3) :
      ∑ p : Fin B × Fin 4, regressionColumns (w p.1) k p.2 * r p = 0 := by
    apply SAP.P037a.WH.W1.P.T1_L3.finite_quadratic_minimum _ _ (hmin_slope k)
  have hrow (k : Fin 3) :
      (∑ l : Fin 3, (∑ b : Fin B,
          centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l)) * theta l) =
        ∑ b : Fin B, centeredCross (regressionColumns (w b) k) (observedOutcome (w b)) := by
    have hres (b : Fin B) :
        (fun i : Fin 4 => observedOutcome (w b) i) =
          (fun i => r (b,i)) + (fun _ => alpha b) +
            (fun i => ∑ l : Fin 3, regressionColumns (w b) l i * theta l) := by
      funext i
      dsimp [r, SAP.P037a.WH.W1.P.T1_L3.residual]
      ring
    have hcenter (b : Fin B) :
        centeredCross (regressionColumns (w b) k) (observedOutcome (w b)) =
          centeredCross (regressionColumns (w b) k) (fun i => r (b,i)) +
            ∑ l : Fin 3, theta l * centeredCross (regressionColumns (w b) k)
              (regressionColumns (w b) l) := by
      calc
        _ = centeredCross (regressionColumns (w b) k)
            (fun i => (r (b,i) + alpha b) +
              ∑ l : Fin 3, regressionColumns (w b) l i * theta l) := by
          exact congrArg (centeredCross (regressionColumns (w b) k)) (hres b)
        _ = centeredCross (regressionColumns (w b) k) (fun i => r (b,i) + alpha b) +
            centeredCross (regressionColumns (w b) k)
              (fun i => ∑ l : Fin 3, regressionColumns (w b) l i * theta l) := by
          exact SAP.P037a.WH.W1.P.T1_L3.centeredCross_add _ _ _
        _ = centeredCross (regressionColumns (w b) k) (fun i => r (b,i)) +
            centeredCross (regressionColumns (w b) k) (fun _ => alpha b) +
              centeredCross (regressionColumns (w b) k)
                (fun i => ∑ l : Fin 3, regressionColumns (w b) l i * theta l) := by
          rw [SAP.P037a.WH.W1.P.T1_L3.centeredCross_add]
        _ = centeredCross (regressionColumns (w b) k) (fun i => r (b,i)) +
            ∑ l : Fin 3, theta l * centeredCross (regressionColumns (w b) k)
              (regressionColumns (w b) l) := by
          rw [SAP.P037a.WH.W1.P.T1_L3.centeredCross_const,
            SAP.P037a.WH.W1.P.T1_L3.centeredCross_sum]
          simp only [add_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro l hl
          have hm := SAP.P037a.WH.W1.P.T1_L3.centeredCross_mul
            (regressionColumns (w b) k) (regressionColumns (w b) l) (theta l)
          simpa [mul_comm] using hm
    have hraw : ∑ b : Fin B, centeredCross (regressionColumns (w b) k)
        (fun i => r (b,i)) = 0 := by
      unfold centeredCross
      rw [Finset.sum_sub_distrib]
      have hprod : (∑ b : Fin B, ∑ i : Fin 4,
          regressionColumns (w b) k i * r (b,i)) =
          ∑ p : Fin B × Fin 4, regressionColumns (w p.1) k p.2 * r p := by
        rw [Fintype.sum_prod_type]
      rw [hprod]
      have hmean : ∑ b : Fin B,
          (∑ i : Fin 4, regressionColumns (w b) k i) * (∑ i : Fin 4, r (b,i)) / 4 = 0 := by
        simp [hinter]
      rw [hmean]
      simpa using hslope k
    have hsumCenter :
        (∑ b : Fin B, centeredCross (regressionColumns (w b) k) (observedOutcome (w b))) =
          (∑ b : Fin B, centeredCross (regressionColumns (w b) k) (fun i => r (b,i))) +
            ∑ b : Fin B, ∑ l : Fin 3, theta l *
              centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l) := by
      calc
        _ = ∑ b : Fin B,
            (centeredCross (regressionColumns (w b) k) (fun i => r (b,i)) +
              ∑ l : Fin 3, theta l * centeredCross (regressionColumns (w b) k)
                (regressionColumns (w b) l)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hcenter b
        _ = _ := by rw [Finset.sum_add_distrib]
    have hcoef :
        (∑ l : Fin 3, (∑ b : Fin B,
          centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l)) * theta l) =
        ∑ b : Fin B, ∑ l : Fin 3, theta l *
          centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l) := by
      calc
        _ = ∑ l : Fin 3, ∑ b : Fin B,
          theta l * centeredCross (regressionColumns (w b) k) (regressionColumns (w b) l) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b hb
            ring
        _ = _ := Finset.sum_comm
    rw [← hcoef, hraw, zero_add] at hsumCenter
    exact hsumCenter.symm
  funext k
  simp only [Matrix.mulVec, dotProduct, SAP.P037a.pooledCompositionGram,
    SAP.P037a.pooledCompositionRhs]
  exact hrow k
