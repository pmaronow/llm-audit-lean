import SAP.P027b.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.Bridge
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

theorem phase_card (r m : ℕ) :
    (Fintype.card (Σ _ : Fin r × Fin 2, Fin m) : ℝ) = (m:ℝ)*(2*r) := by
  simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  push_cast
  ring

theorem periodicMeanV_scale (r m : ℕ) (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
    periodicMeanV hr z = variance (phaseOriginal r m hr) (htTotal (phaseOriginal r m hr) z) /
      ((m:ℝ)*(2*r))^2 := by
  change AronowAudit.P027.variance (AronowAudit.P027.phaseOriginal r m hr)
    (AronowAudit.P027.htMean (AronowAudit.P027.phaseOriginal r m hr) z) = _
  unfold AronowAudit.P027.htMean
  rw [AronowAudit.P027.variance_div_const,phase_card]
  rfl

theorem periodicMeanH_scale (r m : ℕ) (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
    periodicMeanH hr z = expect (phaseOriginal r m hr)
      (htVarianceEstimator (phaseOriginal r m hr) z)/((m:ℝ)*(2*r))^2 := by
  exact AronowAudit.P027.expect_div_const (toProject (phaseOriginal r m hr))
    (htVarianceEstimator (phaseOriginal r m hr) z) (((m:ℝ)*(2*r))^2)

theorem periodicMeanC_scale (r m : ℕ) (hr : 0 < r)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) :
    periodicMeanC hr z = expect (phaseOriginal r m hr)
      (c2Estimator (phaseOriginal r m hr) z)/((m:ℝ)*(2*r))^2 := by
  exact AronowAudit.P027.expect_div_const (toProject (phaseOriginal r m hr))
    (c2Estimator (phaseOriginal r m hr) z) (((m:ℝ)*(2*r))^2)

theorem periodicModel_proof : PeriodicModel := by
  intro Ξ _ μ _ r m hr hm β σ2 hσ ε hε
  let D := phaseOriginal r m hr
  let z := centeredOutcomes phaseSize β ε
  let Y := fun ξ => groupTotal (fun _ : Fin r × Fin 2 => m) (z ξ)
  let q : ℝ := 2*r
  let N : ℝ := m*q
  let L := 16*(m:ℝ)^2*β^2+(m:ℝ)*σ2*(1-1/q)
  let B := fun ξ => (∑ g, Y ξ g^2)/N^2
  let V := outcomeE μ (fun ξ => periodicMeanV hr (z ξ))
  let H := outcomeE μ (fun ξ => periodicMeanH hr (z ξ))
  let C := outcomeE μ (fun ξ => periodicMeanC hr (z ξ))
  let W := outcomeE μ (fun ξ => periodicMeanW hr (z ξ))
  let Q := outcomeE μ (fun ξ => ∑ k, z ξ k^2)
  let Vt := outcomeE μ (fun ξ => variance D (htTotal D (z ξ)))
  let Ht := outcomeE μ (fun ξ => expect D (htVarianceEstimator D (z ξ)))
  let Ct := outcomeE μ (fun ξ => expect D (c2Estimator D (z ξ)))
  have h := AronowAudit.P027.periodic_model_moments μ r m hr (by omega) β σ2 hσ ε hε
  have hb := AronowAudit.P027.periodic_model_bias μ r m hr (by omega) β σ2 ε hε
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN : N ≠ 0 := mul_ne_zero hmR hq
  have hVt : Vt = (9/5)*q^2*L := h.2.2.1
  have hHt : Ht = Vt-q*L := h.2.2.2.1
  have hQ : Q = 16*N*β^2+(N-1)*σ2 := h.2.2.2.2.1
  have hCt : Ct = Ht+(N-m)*Q := h.2.2.2.2.2.1
  have hW : W = (9/5)*σ2/m := h.2.2.2.2.2.2.2.2.2 hm
  have hVscale : V = Vt/N^2 := by
    dsimp [V,Vt,D]
    simp_rw [periodicMeanV_scale]
    exact integral_div _ _
  have hHscale : H = Ht/N^2 := by
    dsimp [H,Ht,D]
    simp_rw [periodicMeanH_scale]
    exact integral_div _ _
  have hCscale : C = Ct/N^2 := by
    dsimp [C,Ct,D]
    simp_rw [periodicMeanC_scale]
    exact integral_div _ _
  have hBscale : outcomeE μ B = q*L/N^2 := by
    calc
      _ = outcomeE μ (fun ξ => ∑ g, Y ξ g^2)/N^2 := integral_div _ _
      _ = _ := congrArg (fun t : ℝ => t/N^2) hb.2.1
  have hB : outcomeE μ B = 16*β^2/q+σ2*(N-m)/N^2 := by
    rw [hBscale]
    dsimp [L,N]
    field_simp
    <;> ring
  have hV : V = (9*q/5)*outcomeE μ B := by
    rw [hVscale,hVt,hBscale]
    ring
  have hH : H = V-outcomeE μ B := by
    rw [hHscale,hHt,hVscale,hBscale]
    ring
  have hC : C = H+(N-m)/N^2*Q := by
    rw [hCscale,hCt,hHscale]
    ring
  change (∀ g, outcomeE μ (fun ξ => Y ξ g^2) = L) ∧
    outcomeE μ B = 16*β^2/q+σ2*(N-m)/N^2 ∧
    V = (9*q/5)*outcomeE μ B ∧ H = V-outcomeE μ B ∧
    (0 < V → (H-V)/V = -5/(9*q)) ∧ Q = 16*N*β^2+(N-1)*σ2 ∧
    C = H+(N-m)/N^2*Q ∧ W = (9/5)*σ2/m ∧ _
  refine ⟨h.1,hB,hV,hH,?_,hQ,hC,hW,?_⟩
  · intro hpos
    apply (div_eq_iff hpos.ne').mpr
    rw [hH,hV]
    field_simp
    <;> ring
  · intro ρ hsig hbeta
    have hqm : N/(m:ℝ) = q := by dsimp [N]; field_simp
    change (V,H,C,W) = periodicModelPredictions N m ρ ∧ Q = 900*(N-1)
    constructor
    · dsimp only [periodicModelPredictions]
      rw [hqm]
      rw [hC,hH,hV,hW,hQ,hB]
      rw [hsig,hbeta]
    · rw [hQ]
      change 16*N*β^2+(N-1)*σ2 = 900*(N-1)
      rw [show β^2 = 900*ρ^2*(N-1)/(16*N) from hbeta,hsig]
      field_simp
      <;> ring

end
end SAP.P027b.Bridge
