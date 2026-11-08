import SAP.P001e.WH.W4.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BigOperators Topology

namespace SAP.P001e.WH.W4.P.T93_L1

theorem normal_equations {n K : ℕ} (Y D : Fin n → ℝ)
    (X : Fin n → Fin K → ℝ) (a b : ℝ) (c : Fin K → ℝ)
    (hfit : SAP.P001e.IsPooledOLSW4 Y D X a b c) :
    (∑ i, (Y i - (a + ∑ k, X i k * c k) - b * D i)) = 0 ∧
    (∑ i, D i * (Y i - (a + ∑ k, X i k * c k) - b * D i)) = 0 := by
  let e : Fin n → ℝ := fun i => Y i - (a + ∑ k, X i k * c k) - b * D i
  let f : ℝ → ℝ := fun t => ∑ i, (e i - t) ^ 2
  let g : ℝ → ℝ := fun t => ∑ i, (e i - t * D i) ^ 2
  have hbasef : SAP.P001e.pooledRSSW4 Y D X a b c = f 0 := by
    simp only [SAP.P001e.pooledRSSW4, SAP.P001e.pooledPredictionW4, f]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [e]
    ring
  have hbaseg : SAP.P001e.pooledRSSW4 Y D X a b c = g 0 := by
    simp only [SAP.P001e.pooledRSSW4, SAP.P001e.pooledPredictionW4, g]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [e]
    ring
  have hshiftf (t : ℝ) :
      SAP.P001e.pooledRSSW4 Y D X (a + t) b c = f t := by
    simp only [SAP.P001e.pooledRSSW4, SAP.P001e.pooledPredictionW4, f]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [e]
    ring
  have hshiftg (t : ℝ) :
      SAP.P001e.pooledRSSW4 Y D X a (b + t) c = g t := by
    simp only [SAP.P001e.pooledRSSW4, SAP.P001e.pooledPredictionW4, g]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [e]
    ring
  have hminf : IsLocalMin f 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, f 0 ≤ f t
    filter_upwards [] with t
    have h := hfit (a + t) b c
    rw [hbasef, hshiftf t] at h
    exact h
  have hming : IsLocalMin g 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, g 0 ≤ g t
    filter_upwards [] with t
    have h := hfit a (b + t) c
    rw [hbaseg, hshiftg t] at h
    exact h
  have hderivf : HasDerivAt f (-2 * ∑ i, e i) 0 := by
    have hterms : ∀ i ∈ Finset.univ,
        HasDerivAt (fun t : ℝ => (e i - t) ^ 2) (-2 * e i) 0 := by
      intro i hi
      convert ((hasDerivAt_id (0 : ℝ)).const_sub (e i)).pow 2 using 1
      · funext t
        rfl
      · norm_num
    simpa [f, Finset.mul_sum] using
      (HasDerivAt.fun_sum (u := Finset.univ) hterms)
  have hderivg : HasDerivAt g (-2 * ∑ i, D i * e i) 0 := by
    have hterms : ∀ i ∈ Finset.univ,
        HasDerivAt (fun t : ℝ => (e i - t * D i) ^ 2) (-2 * (D i * e i)) 0 := by
      intro i hi
      convert (((hasDerivAt_id (0 : ℝ)).mul_const (D i)).const_sub (e i)).pow 2 using 1
      · funext t
        simp
      · norm_num
        ring
    simpa [g, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.fun_sum (u := Finset.univ) hterms)
  have hsum : -2 * ∑ i, e i = 0 := hminf.hasDerivAt_eq_zero hderivf
  have hdsum : -2 * ∑ i, D i * e i = 0 := hming.hasDerivAt_eq_zero hderivg
  constructor <;> linarith

end SAP.P001e.WH.W4.P.T93_L1

theorem SAP.P001e.WH.W4.T93_L1_proof : SAP.P001e.WH.W4.T93_L1 := by
  intro n K Y D X a b c hfit
  exact SAP.P001e.WH.W4.P.T93_L1.normal_equations Y D X a b c hfit
