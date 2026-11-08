import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

theorem SAP.P002a.WH.W2.T5_L4_proof : SAP.P002a.WH.W2.T5_L4 := by
  intro n k P δ e A B r hk he hXi
  classical
  rcases hXi with ⟨hvalid, _, _, _, _, _, _, _, hFourth, hRayleigh⟩
  let s : Fin k := ⟨0, by omega⟩
  let b : Fin k → ℝ := fun t => if t = s then 1 else 0
  have hnorm : SAP.P002a.normSq b = 1 := by
    change (∑ i : Fin k, (if i = s then (1 : ℝ) else 0)^2) = 1
    rw [Finset.sum_eq_single s]
    · simp
    · intro i hi his
      simp [his]
    · simp
  have hdot (i : Fin n) : dotProduct (P.x i) b = P.x i s := by
    change (∑ j : Fin k, P.x i j * (if j = s then (1 : ℝ) else 0)) = P.x i s
    rw [Finset.sum_eq_single s]
    · simp
    · intro j hj hjs
      simp [hjs]
    · simp
  have hsecond : e ≤ SAP.P002a.mean (fun i : Fin n => (P.x i s)^2) := by
    simpa [hnorm, hdot] using hRayleigh b
  have hfourth : SAP.P002a.mean (fun i : Fin n => (P.x i s)^4) ≤ A :=
    hFourth s
  have hsum := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin n => (P.x i s)^2)
  have hsum2 : (∑ i : Fin n, (P.x i s)^2)^2 ≤
      (n : ℝ) * ∑ i : Fin n, ((P.x i s)^2)^2 := by
    simpa using hsum
  have hpow : (∑ i : Fin n, ((P.x i s)^2)^2) =
      ∑ i : Fin n, (P.x i s)^4 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsum' : (∑ i : Fin n, (P.x i s)^2)^2 ≤
      (n : ℝ) * ∑ i : Fin n, (P.x i s)^4 := by
    rw [← hpow]
    exact hsum2
  have hn : (n : ℝ) ≠ 0 := by
    have h2n := hvalid.1
    have hnNat : 0 < n := by omega
    exact_mod_cast (ne_of_gt hnNat)
  have hmoment :
      (SAP.P002a.mean (fun i : Fin n => (P.x i s)^2))^2 ≤
        SAP.P002a.mean (fun i : Fin n => (P.x i s)^4) := by
    change ((∑ i : Fin n, (P.x i s)^2) / (n : ℝ))^2 ≤
      (∑ i : Fin n, (P.x i s)^4) / (n : ℝ)
    rw [div_pow]
    calc
      (∑ i : Fin n, (P.x i s)^2)^2 / (n : ℝ)^2 ≤
          ((n : ℝ) * ∑ i : Fin n, (P.x i s)^4) / (n : ℝ)^2 :=
        div_le_div_of_nonneg_right hsum' (sq_nonneg (n : ℝ))
      _ = (∑ i : Fin n, (P.x i s)^4) / (n : ℝ) := by
        field_simp [hn]
  have hsquare : e^2 ≤ (SAP.P002a.mean (fun i : Fin n => (P.x i s)^2))^2 :=
    (sq_le_sq₀ (le_of_lt he) (le_trans (le_of_lt he) hsecond)).2 hsecond
  exact le_trans hsquare (le_trans hmoment hfourth)
