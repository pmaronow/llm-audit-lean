import AronowAudit.P015.P015_PaperSpecializations
import AronowAudit.P015.P015_RandomizationCompletion

namespace AronowAudit.P015.PaperDomains
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

/-- The actual binary response likelihood on its open admissible link domain,
including the intercept and treatment/control coordinates of Appendix C. -/
theorem likelihood_directional_derivative (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0<m η ∧ m η<1)
    (θ v : Fin (K+2) → ℝ) (hθ : ∀ i, W.mulVec θ i∈I) :
    HasDerivAt (fun t : ℝ => groupedLikelihood W (fun _ => 1) Y m (θ+t • v))
      (∑ i, scoreMultiplier m (W.mulVec θ i)*(Y i-m (W.mulVec θ i))*W.mulVec v i) 0 := by
  simpa only [Pi.add_def,Pi.smul_def,smul_eq_mul,one_mul] using
    AronowAudit.P015.likelihood_directional_derivative_calculus W (fun _ => 1) Y m θ v
    (fun i => (hm _ (hθ i)).differentiableAt (hI.mem_nhds (hθ i)))
    (fun i => (hprob _ (hθ i)).1) (fun i => (hprob _ (hθ i)).2)

/-- An actual finite logistic ML maximizer satisfies every score equation.
The stationarity needed by the exact remainder identity is derived here. -/
theorem logistic_ML_score_zero (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1)
    (θ : Fin (K+2) → ℝ)
    (hmax : ∀ γ, groupedLikelihood W (fun _ => 1) Y logistic γ ≤
      groupedLikelihood W (fun _ => 1) Y logistic θ) :
    groupedResidual W (fun _ => 1) Y logistic θ=0 := by
  ext j
  let v : Fin (K+2) → ℝ := Pi.single j 1
  let F : ℝ → ℝ := fun t => groupedLikelihood W (fun _ => 1) Y logistic (θ+t • v)
  have hd := AronowAudit.P015.likelihood_directional_derivative_calculus W
    (fun _ => 1) Y logistic θ v (fun _ => differentiableAt_sigmoid)
    (fun _ => Real.sigmoid_pos _) (fun _ => Real.sigmoid_lt_one _)
  have hlocal : IsLocalMax F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [F] using hmax (θ+t • v)
  have hz := hlocal.hasDerivAt_eq_zero hd
  simpa [v,groupedResidual,Matrix.mulVec,dotProduct,Pi.single_apply,logistic_multiplier,mul_comm]
    using hz

/-- The exact coefficient remainder for an actual binary logistic ML fit. -/
theorem logistic_exact_remainder (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (hQ : (W.transpose*W).det≠0) (b c : ℝ) (θ : Fin (K+2) → ℝ)
    (hmax : ∀ γ, groupedLikelihood W (fun _ => 1) Y logistic γ ≤
      groupedLikelihood W (fun _ => 1) Y logistic θ) :
    let R := fun i => logistic (W.mulVec θ i)-(b+c*W.mulVec θ i)
    ols W Y=affineTheta 0 b c θ+(W.transpose*W)⁻¹.mulVec (W.transpose.mulVec R) :=
  AronowAudit.P015.logistic_exact_remainder W 0 hW Y hQ b c θ
    (logistic_ML_score_zero N K W Y hY θ hmax)

/-- Appendix A's fitted treatment residuals, with their literal OLS
coefficient error and the sample-average normalization used in T23. -/
theorem residual_weight_expansion {Ω : Type*} {K : ℕ}
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (ω : Fin (K+1) → ℝ) (n : ℕ) (s : Ω) :
    let r := fun i : Fin n => D i s-dotProduct (controlRow (X i s)) ω
    let e := fun i : Fin n => dotProduct (controlRow (X i s)) (omegaHat D X n s-ω)
    (∑ i : Fin n, residualHat D X n s i^2*Z i s)/(n:ℝ)=
      ((∑ i : Fin n, r i^2*Z i s)-2*(∑ i : Fin n, r i*Z i s*e i)+(∑ i : Fin n, Z i s*e i^2))/(n:ℝ) := by
  dsimp only
  have he : ∀ i : Fin n, residualHat D X n s i=
      (D i s-dotProduct (controlRow (X i s)) ω)-
        dotProduct (controlRow (X i s)) (omegaHat D X n s-ω) := by
    intro i
    simp only [residualHat,sampleResidual,designV,Matrix.mulVec,dotProduct_sub]
    ring
  simp_rw [he]
  exact congrArg (fun t : ℝ => t/(n:ℝ))
    (AronowAudit.P015.residual_weight_expansion
      (fun i : Fin n => D i s-dotProduct (controlRow (X i s)) ω)
      (fun i : Fin n => dotProduct (controlRow (X i s)) (omegaHat D X n s-ω))
      (fun i : Fin n => Z i s))

/- T8(iv): the exact first Taylor polynomial replaces the unjustified
quadratic remainder under mere twice differentiability. -/
theorem full_score_firstTaylor_repair (N K : ℕ)
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


theorem likelihood_directional_derivative_calculus (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0<m η ∧ m η<1)
    (θ v : Fin (K+2) → ℝ) (hθ : ∀ i, W.mulVec θ i∈I) :
    HasDerivAt (fun t : ℝ => groupedLikelihood W (fun _ => 1) Y m (θ+t • v))
      (∑ i, scoreMultiplier m (W.mulVec θ i)*(Y i-m (W.mulVec θ i))*W.mulVec v i) 0 := by
  simpa only [Pi.add_def,Pi.smul_def,smul_eq_mul,one_mul] using
    AronowAudit.P015.likelihood_directional_derivative_calculus W (fun _ => 1) Y m θ v
    (fun i => (hm _ (hθ i)).differentiableAt (hI.mem_nhds (hθ i)))
    (fun i => (hprob _ (hθ i)).1) (fun i => (hprob _ (hθ i)).2)


end
end AronowAudit.P015.PaperDomains
