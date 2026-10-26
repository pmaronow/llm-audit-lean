import AronowAudit.P015.P015_Regression


namespace AronowAudit.P015.PaperSpecializations
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

theorem finite_unconfounded_algebra {A B C : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (g : B → C) (D : A → ℝ) (hlaw : IsLaw p) :
    fCondIndep p X (fun a => g (X a)) D := by
  exact AronowAudit.P015.finite_unconfounded (A := A) (B := B) (C := C) (p := p) (X := X) (g := g) (D := D) (hlaw := hlaw)

theorem rare_profile_ratio_bound (ε : ℝ) (hε : 0 < ε) (hu : ε < 1/2) :
    IsLaw (rareLaw ε) ∧
    (∀ a d, rareY a d = rareY a 0+(1+binaryX a)*d) ∧
    fCondIndep (rareLaw ε) binaryX (fun a => (rareY a 0,1+binaryX a)) binaryD ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      fCondMean (rareLaw ε) binaryX binaryD x = ε+(1/2-ε)*x ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 0 ∧
      0 < fCondProb (rareLaw ε) binaryX binaryD x 1) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) ∧
    0 < fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) ∧
    fMass (fEffective (rareLaw ε) binaryX binaryD) (fun a => binaryX a=0) < 4*ε := by
  exact AronowAudit.P015.rare_profile_bound (ε := ε) (hε := hε) (hu := hu)

theorem bernoulli_score_derivative_calculus (m : ℝ → ℝ) (y η m' : ℝ)
    (hy : y=0 ∨ y=1) (hm : HasDerivAt m m' η) (hp : 0<m η) (hu : m η<1) :
    HasDerivAt (binomialLogLikelihood m 1 y) (m'/(m η*(1-m η))*(y-m η)) η := by
  exact AronowAudit.P015.bernoulli_score_derivative (m := m) (y := y) (η := η) (m' := m') (hy := hy) (hm := hm) (hp := hp) (hu := hu)

theorem canonical_score_derivative_calculus (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ)
    (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : CanonicalFamily ν κ s carrier I support)
    (y η κ' : ℝ) (hy : y∈support) (hη : η∈I) (hk : HasDerivAt κ κ' η) :
    HasDerivAt (canonicalLogLikelihood κ s y (carrier y)) ((y-κ')/s) η := by
  exact AronowAudit.P015.canonical_score_derivative (ν := ν) (κ := κ) (s := s) (carrier := carrier) (I := I) (support := support) (hfamily := hfamily) (y := y) (η := η) (κ' := κ') (hy := hy) (hη := hη) (hk := hk)

theorem scalar_full_score_firstTaylor (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0<m η ∧ m η<1)
    (η₀ p₀ : ℝ) (hη : η₀∈I) (hp : 0<p₀) (hu : p₀<1) (hmean : m η₀=p₀)
    (hm₂ : DifferentiableAt ℝ (deriv m) η₀) :
    let θ₀ : Fin (K+2) → ℝ := fun j => if j=0 then η₀ else 0
    let h := scoreMultiplier m
    let h₀ := h η₀
    let f₀ := deriv m η₀
    let h₁ := deriv h η₀
    let r := W.transpose.mulVec (fun i => Y i-p₀)
    let A := W.transpose*W
    let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ := fun j k => ∑ i, (Y i-p₀)*W i j*W i k
    ∀ δ : Fin (K+2) → ℝ,
      (fun j => ∑ i, W i j*firstTaylor (fun η => h η*(Y i-m η)) η₀ (W.mulVec (θ₀+δ) i)) =
        h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ := by
  exact AronowAudit.P015.full_score_firstTaylor (N := N) (K := K) (W := W) (Y := Y) (hY := hY) (hW := hW) (I := I) (hI := hI) (m := m) (hm := hm) (hprob := hprob) (η₀ := η₀) (p₀ := p₀) (hη := hη) (hp := hp) (hu := hu) (hmean := hmean) (hm₂ := hm₂)

theorem probit_residual_conditional : ProbitCounterexample := by
  exact AronowAudit.P015.ProbitCounterexample_checked

theorem spending_mean_arithmetic :
    let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
    let S : Fin 4 → ℝ := ![1,1,0,3]
    let Y := fun i => Real.log ((1+S i)/2)
    ols W Y 1=0 ∧ Real.exp (ols W Y 1)=1 ∧
    (Real.log (1/2)+Real.log 2)/2=0 ∧
    (S 0+S 1)/2=1 ∧ (S 2+S 3)/2=3/2 ∧ ((3/2:ℝ)/1-1)*100=50 := by
  exact AronowAudit.P015.spending_mean_counterexample

theorem binary_variance_reversal_arithmetic : PositivityCorrection := by
  exact AronowAudit.P015.PositivityCorrection_checked

theorem finite_chebyshev_algebra {A : Type*} [Fintype A] (p Z : A → ℝ)
    (hlaw : IsLaw p) (δ : ℝ) (hδ : 0 < δ) :
    fMass p (fun a => δ ≤ |Z a-fExpectation p Z|) ≤ fVariance p Z/δ^2 := by
  exact AronowAudit.P015.finite_chebyshev (A := A) (p := p) (Z := Z) (hlaw := hlaw) (δ := δ) (hδ := hδ)

theorem iid_tensor_expectation_algebra {A : Type*} [Fintype A] (p : A → ℝ)
    (hlaw : IsLaw p) (n : ℕ) (G : Fin n → A → ℝ) :
    fExpectation (iidLaw p n) (fun a => ∏ i, G i (a i)) =
      ∏ i, fExpectation p (G i) := by
  exact AronowAudit.P015.iid_tensor_expectation (A := A) (p := p) (hlaw := hlaw) (n := n) (G := G)

theorem scalar_pooling_iff_algebra (G q : ℕ) (hG : 1≤G) (hq : 1≤q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (S : Matrix (Fin q) (Fin q) ℝ) (σ₂ : Fin G → ℝ) (hS : S.PosSemidef)
    (hσ : ∀ g, 0<σ₂ g) (hQ : ∀ g, ((Z g).transpose*Z g).det≠0)
    (a : Fin G → ℝ) (b : Fin q) :
    let P := fun g => groupPrecision S ((Z g).transpose*Z g) (σ₂ g)
    let A := fun g => (∑ h, P h)⁻¹*P g
    (∀ t : Fin G → Fin q → ℝ, (∑ g, ∑ j, A g b j*t g j)=∑ g, a g*t g b) ↔
      ∀ g j, A g b j=if j=b then a g else 0 := by
  exact AronowAudit.P015.scalar_pooling_iff (G := G) (q := q) (hG := hG) (hq := hq) (n := n) (Z := Z) (S := S) (σ₂ := σ₂) (hS := hS) (hσ := hσ) (hQ := hQ) (a := a) (b := b)

theorem odds_not_mle_calculus : OddsCounterexample := by
  exact AronowAudit.P015.OddsCounterexample_checked

theorem odds_gram_determinant : OddsCounterexample := by
  exact AronowAudit.P015.OddsCounterexample_checked

theorem regression_decomposition_algebra (n K : ℕ) (D Y₀ τ : Fin n → ℝ) (X : Fin n → Fin K → ℝ)
    (hQ : Matrix.det ((fun j k : Fin (K+2) =>
      ∑ i : Fin n, regressorRow (D i) (X i) j*regressorRow (D i) (X i) k) :
      Matrix (Fin (K+2)) (Fin (K+2)) ℝ)≠0) :
    let V : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => controlRow (X i)
    let W : Matrix (Fin n) (Fin (K+2)) ℝ := fun i => regressorRow (D i) (X i)
    let m := V.mulVec (ols V D)
    let r := sampleResidual V D (ols V D)
    ols W (fun i => Y₀ i+τ i*D i) 1=
      (∑ i, r i*Y₀ i)/(∑ i, r i^2)+
      (∑ i, r i*m i*τ i)/(∑ i, r i^2)+
      (∑ i, r i^2*τ i)/(∑ i, r i^2) := by
  exact AronowAudit.P015.regression_decomposition (n := n) (K := K) (D := D) (Y₀ := Y₀) (τ := τ) (X := X) (hQ := hQ)

theorem rare_ols_arithmetic : RareCounterexample := by
  exact AronowAudit.P015.RareCounterexample_checked

theorem common_support_arithmetic : MultivaluedCounterexample := by
  exact AronowAudit.P015.MultivaluedCounterexample_checked

theorem finite_variance_zero_iff : PositivityCorrection := by
  exact AronowAudit.P015.PositivityCorrection_checked

theorem finite_variance_pos_of_atoms : PositivityCorrection := by
  exact AronowAudit.P015.PositivityCorrection_checked

theorem observational_equality_no_two_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (draw : ℕ → Ω → Fin 4)
    (hdraw : MultiSampling P draw) (T : ∀ n : ℕ, (Fin n → ℝ × ℝ × ℝ) → ℝ) :
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (2:ℝ))) ∧
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => multivaluedObserved worldB (draw i s))) atTop (fun _ => (13/5:ℝ))) := by
  exact AronowAudit.P015.no_common_consistent_estimator (Ω := Ω) (P := P) (draw := draw) (hdraw := hdraw) (T := T)

theorem zero_sample_ols_arithmetic : FittedZeroCounterexample := by
  exact AronowAudit.P015.FittedZeroCounterexample_checked

theorem rare_ipw_tail_convergence : RareCounterexample := by
  exact AronowAudit.P015.RareCounterexample_checked

theorem canonical_common_score_calculus {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1)
    (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : CanonicalFamily ν κ s carrier I support)
    (Y : N → ℝ) (hY : ∀ i, Y i∈support) (θ : Q → ℝ)
    (hθ : ∀ i, W.mulVec θ i∈I) (hκ : ∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)) :
    (∀ v : Q → ℝ, HasDerivAt
      (fun t => canonicalLikelihood W κ s (fun i => Y i) (fun i => carrier (Y i)) (fun j => θ j+t*v j))
      (s⁻¹*(∑ i, (Y i-deriv κ (W.mulVec θ i))*W.mulVec v i)) 0) ∧
    ((∀ j, s⁻¹*(∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) ↔
      ∀ j, (∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) := by
  exact AronowAudit.P015.canonical_common_score (N := N) (Q := Q) (W := W) (j₀ := j₀) (hW := hW) (ν := ν) (κ := κ) (s := s) (carrier := carrier) (I := I) (support := support) (hfamily := hfamily) (Y := Y) (hY := hY) (θ := θ) (hθ := hθ) (hκ := hκ)

end
end AronowAudit.P015.PaperSpecializations
