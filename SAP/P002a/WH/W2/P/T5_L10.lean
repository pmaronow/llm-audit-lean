import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L10

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a
attribute [local instance] Classical.propDecidable

private theorem cube_mean_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Fin n → ℝ) :
    mean (fun i => ∑ s, f s i) = ∑ s, mean (fun i => f s i) := by
  unfold mean
  rw [Finset.sum_comm]
  rw [← Finset.sum_div]

private theorem cube_mean_const_mul {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    mean (fun i => c * f i) = c * mean f := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem proof_impl : SAP.P002a.WH.W2.T5_L10 := by
  intro h9 k δ e A B r hk hδ hδ' he hA hB hr j
  let P := W2CubeModel k e j
  let m : ℕ := 2^k * (j+1)
  let n : ℕ := W2CubeSize k j
  have hsize : W2CubeSize k j = 2*m := by
    dsimp [m, W2CubeSize]
    rw [pow_succ]
    ring
  have hn : n = 2*m := by
    exact hsize
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hN : 0 < n := by omega
  have hN2 : 2 ≤ n := by omega
  have hNcast : (n : ℝ) ≠ 0 := by positivity
  have hn1 : P.pop.n1 = m := by
    change W2CubeSize k j / 2 = m
    rw [hsize]
    omega
  have hn1cast : (P.pop.n1 : ℝ) = (n : ℝ)/2 := by
    rw [hn1]
    change (m : ℝ) = (W2CubeSize k j : ℝ)/2
    rw [hsize]
    push_cast
    ring
  have hmean_univ (f : Fin n → ℝ) : groupMean Finset.univ f = mean f := by
    simp [groupMean, mean]
  have hmean_one : mean (fun _ : Fin n => (1 : ℝ)) = 1 := by
    unfold mean
    have hs : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
    rw [hs]
    exact div_self hNcast
  have hL9 := h9 k e j hk he
  rcases hL9 with ⟨hy0, hy2, hy4, hx0, hxx, hx4, hxy⟩
  have hy0P : (∑ i, P.pop.y i false) = 0 := by simpa [P] using hy0
  have hx0P (s : Fin k) : (∑ i, P.x i s) = 0 := by simpa [P] using hx0 s
  have hy2P : mean (fun i => P.pop.y i false ^ 2) = 1 := by simpa [P] using hy2
  have hy4P : mean (fun i => P.pop.y i false ^ 4) = 1 := by simpa [P] using hy4
  have hx4P (s : Fin k) : mean (fun i => P.x i s ^ 4) = e^2 := by simpa [P] using hx4 s
  have hxyP (s : Fin k) : mean (fun i => P.x i s * P.pop.y i false) = 0 := by
    simpa [P] using hxy s
  have hxxP (s t : Fin k) : mean (fun i => P.x i s * P.x i t) = if s=t then e else 0 := by
    simpa [P] using hxx s t
  have hymean : mean (fun i => P.pop.y i false) = 0 := by
    unfold mean
    rw [hy0P]
    simp
  have hxmean (s : Fin k) : mean (fun i => P.x i s) = 0 := by
    unfold mean
    rw [hx0P s]
    simp
  have hysqsum : (∑ i, (P.pop.y i false)^2) = (n : ℝ) := by
    have h' : (∑ i, (P.pop.y i false)^2) / (n : ℝ) = 1 := by
      simpa [mean] using hy2P
    have heq := (div_eq_iff hNcast).mp h'
    nlinarith
  have hvar : popVar (fun i => P.pop.y i false) = (n : ℝ)/((n : ℝ)-1) := by
    unfold popVar
    rw [hymean]
    simp only [sub_zero]
    rw [hysqsum]
  have hvarpos : 0 < popVar (fun i => P.pop.y i false) := by
    rw [hvar]
    have : (0 : ℝ) < (n : ℝ)-1 := by
      have hnlarge : 1 < n := by omega
      have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hnlarge
      linarith
    positivity
  have hvarone : 1 ≤ popVar (fun i => P.pop.y i false) := by
    rw [hvar]
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN2
    have hden : 0 < (n : ℝ)-1 := by linarith
    rw [le_div_iff₀ hden]
    linarith
  have hcovar : popCov (fun i => P.pop.y i false) (fun i => P.pop.y i false) =
      popVar (fun i => P.pop.y i false) := by
    simp only [popCov, popVar, hymean, sub_zero, pow_two]
  have hcomp : compliers P.pop = Finset.univ := by
    ext i
    simp [compliers, P, W2CubeModel]
  have hlate : late P.pop = 0 := by
    unfold late
    rw [hcomp]
    simp [groupMean, P, W2CubeModel]
  have hscore : score P.x Finset.univ (fun i => P.pop.y i false) = 0 := by
    ext a
    cases a with
    | none =>
        change groupMean Finset.univ (fun i => (1 : ℝ) * P.pop.y i false) = 0
        simpa [hmean_univ] using hymean
    | some s =>
        simpa [score, augmented, hmean_univ] using hxyP s
  have hxgroup (s : Fin k) : groupMean Finset.univ (fun i => P.x i s) = 0 := by
    rw [hmean_univ]
    exact hxmean s
  have hgroupOne : groupMean Finset.univ (fun _ : Fin n => (1 : ℝ)) = 1 := by
    rw [hmean_univ]
    exact hmean_one
  have hgram : gram P.x Finset.univ =
      Matrix.diagonal (fun a : Option (Fin k) => if a.isNone then 1 else e) := by
    ext a b
    cases a with
    | none =>
        cases b with
        | none =>
            simpa [gram, augmented, Matrix.diagonal_apply] using hgroupOne
        | some t =>
            simpa [gram, augmented, Matrix.diagonal_apply] using hxgroup t
    | some s =>
        cases b with
        | none =>
            simpa [gram, augmented, Matrix.diagonal_apply] using hxgroup s
        | some t =>
            simpa [gram, augmented, Matrix.diagonal_apply, hmean_univ] using hxxP s t
  have hdet : (gram P.x Finset.univ).det ≠ 0 := by
    rw [hgram, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    cases a with
    | none => simp
    | some s => exact ne_of_gt he
  have hpsi (a : Bool) : psi P a 0 = 0 := by
    have hw : w P.pop a 0 = fun i => P.pop.y i false := by
      funext i
      simp [w, P, W2CubeModel]
    change ols P.x Finset.univ (w P.pop a 0) = 0
    rw [hw]
    unfold ols
    rw [if_pos hdet]
    rw [hscore]
    simp
  have hres (a : Bool) : residual P a 0 = fun i => P.pop.y i false := by
    funext i
    rw [residual, hpsi]
    simp [w, P, W2CubeModel]
  have hquad (b : Fin k → ℝ) :
      mean (fun i => (dotProduct (P.x i) b)^2) = e * normSq b := by
    calc
      mean (fun i => (dotProduct (P.x i) b)^2) =
          ∑ s, ∑ t, b s * b t * mean (fun i => P.x i s * P.x i t) := by
        simp only [dotProduct, pow_two]
        calc
          mean (fun i => (∑ s, P.x i s * b s) * (∑ t, P.x i t * b t)) =
              mean (fun i => ∑ s, ∑ t, (P.x i s * b s) * (P.x i t * b t)) := by
                congr 1
                funext i
                rw [Finset.sum_mul_sum]
          _ = ∑ s, ∑ t, mean (fun i => (P.x i s * b s) * (P.x i t * b t)) := by
                rw [cube_mean_sum]
                apply Finset.sum_congr rfl
                intro s hs
                rw [cube_mean_sum]
          _ = ∑ s, ∑ t, b s * b t * mean (fun i => P.x i s * P.x i t) := by
                apply Finset.sum_congr rfl
                intro s hs
                apply Finset.sum_congr rfl
                intro t ht
                rw [show (fun i => (P.x i s * b s) * (P.x i t * b t)) =
                  (fun i => (b s * b t) * (P.x i s * P.x i t)) by
                    funext i
                    ring]
                exact cube_mean_const_mul _ _
      _ = e * normSq b := by
        simp [normSq, hxxP]
        calc
          ∑ x, b x * b x * e = ∑ x, e * b x ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = e * ∑ j, b j ^ 2 := by rw [Finset.mul_sum]
  have hXi : Xi P δ e A B r := by
    refine ⟨⟨hN2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hn1]
      exact hm
    · rw [hn1]
      change m < W2CubeSize k j
      rw [hsize]
      omega
    · intro i hd
      have : False := by simpa [P, W2CubeModel] using hd
      exact this.elim
    · rw [hcomp]
      change (Finset.univ : Finset (Fin (W2CubeSize k j))).Nonempty
      exact ⟨⟨0, by rw [hsize]; omega⟩, Finset.mem_univ _⟩
    · rw [hn1cast]
      nlinarith [hr.1]
    · rw [hn1cast]
      nlinarith [hr.2]
    · rw [hlate, hres true, hres false, hcovar]
      have hroot : Real.sqrt (popVar (fun i => P.pop.y i false)) ^ 2 =
          popVar (fun i => P.pop.y i false) := Real.sq_sqrt (le_of_lt hvarpos)
      have hcoef : -δ ≤ 1 := by linarith
      nlinarith [hroot]
    · intro a
      rw [hlate, hres a]
      have hfourth : fourthNorm (fun i => P.pop.y i false) = 1 := by
        simp [fourthNorm, hy4P]
      rw [hfourth]
      have hsqrt : 1 ≤ Real.sqrt (popVar (fun i => P.pop.y i false)) :=
        Real.one_le_sqrt.mpr hvarone
      nlinarith [hsqrt]
    · refine ⟨hx0P, ?_, ?_⟩
      · intro s
        rw [hx4P s]
        exact hA
      · intro b
        rw [hquad b]
  refine ⟨hXi, ?_, ?_, ?_⟩
  · exact hlate
  · intro a
    change residual P a 0 = fun i => P.pop.y i false
    exact hres a
  · change 0 < popVar (residual P false (late P.pop))
    rw [hlate, hres false]
    exact hvarpos

end

end SAP.P002a.WH.W2.P.T5_L10

theorem SAP.P002a.WH.W2.T5_L10_proof : SAP.P002a.WH.W2.T5_L10 :=
  SAP.P002a.WH.W2.P.T5_L10.proof_impl
