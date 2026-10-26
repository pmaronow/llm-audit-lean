import AronowAudit.P039.P039_Regression
namespace AronowAudit.P039.PaperDomains
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Literal T4(f) covariance assertion, before adding the necessary positive-noise domain. -/
def LiteralCovarianceClaim : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) (γ : Fin k → ℝ)
    (ε : Ω → Fin n → ℝ) (σ : ℝ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hij : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hc : vectorCovariance μ ε = σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)),
    let M := residualMaker Z
    let r := fun ω => M *ᵥ (Z *ᵥ γ + ε ω)
    (vectorCovariance μ r).rank = n-k ∧
      vectorCovariance μ r ≠ σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma witness_intercept : ∃ c, witnessZ *ᵥ c = fun _ => (1 : ℝ) := by
  refine ⟨![1,0], ?_⟩
  ext i; fin_cases i <;> norm_num [witnessZ,witnessU,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
lemma witness_outside : ¬ ∃ c, witnessZ *ᵥ c = witnessV := by
  rintro ⟨c,h⟩
  have h2 := congrFun h (2 : Fin 6)
  have h3 := congrFun h (3 : Fin 6)
  norm_num [witnessZ,witnessU,witnessV,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h2 h3
  linarith

/-- An actual zero-noise OLS model refutes the unguarded covariance assertion. -/
theorem zero_noise_refutes_literal_covariance : ¬ LiteralCovarianceClaim := by
  intro h
  have hc : vectorCovariance (Measure.dirac ()) (fun _ : Unit => (0 : Fin 6 → ℝ)) =
      (0 : ℝ)^2 • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
    ext i j; simp [vectorCovariance]
  have hh := h (Ω := Unit) (Measure.dirac ()) witnessZ witnessV (0 : Fin 2 → ℝ)
    (fun _ : Unit => (0 : Fin 6 → ℝ)) 0 witness_baseline.2.2.1 witness_intercept
    witness_outside (by norm_num) (fun _ => Integrable.of_finite)
    (fun _ _ => Integrable.of_finite) (fun _ => by simp) hc
  dsimp only at hh
  have hz : (fun _ : Unit => residualMaker witnessZ *ᵥ
      (witnessZ *ᵥ (0 : Fin 2 → ℝ)+(0 : Fin 6 → ℝ))) = fun _ => 0 := by
    funext ω; simp
  rw [hz] at hh
  have hcov : vectorCovariance (Measure.dirac ()) (fun _ : Unit => (0 : Fin 6 → ℝ)) = 0 := by
    ext i j; simp [vectorCovariance]
  rw [hcov] at hh
  norm_num at hh

/-- Complete covariance and distributional assessment: the literal zero-noise extension is false;
all covariance-rank conclusions hold on the explicitly corrected positive-noise domain. -/
theorem corrected_residual_covariance_assessment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) (γ : Fin k → ℝ)
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hZ : FullColumnRank Z) (h1 : ∃ c, Z *ᵥ c = fun _ => 1)
    (hx : ¬ ∃ c, Z *ᵥ c = x) (hn : k+1 < n)
    (hi : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hij : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ)
    (he : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hc : vectorCovariance μ ε = σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    let M := residualMaker Z
    let r := fun ω => M *ᵥ (Z *ᵥ γ + ε ω)
    let xc := x - ((∑ i, x i) / n) • (fun _ => (1 : ℝ))
    let tf := fun ω => olsT (fullDesign Z x) (Z *ᵥ γ + ε ω) (Fin.last k)
    let tr := fun ω => olsT (residualLine x) (r ω) 1
    (∀ ω, r ω = M *ᵥ ε ω) ∧
    vectorCovariance μ r = σ^2 • M ∧ M.rank = n-k ∧
    (vectorCovariance μ r).rank = n-k ∧
    vectorCovariance μ r ≠ σ^2 • (1 : Matrix (Fin n) (Fin n) ℝ) ∧
    (2 ≤ k → controlProjection Z *ᵥ xc = 0 → μ.map tf = studentLaw (n-k-1) →
      μ.map tr = (studentLaw (n-k-1)).map
        (fun t => Real.sqrt (((n : ℝ)-2)/((n : ℝ)-k-1))*t) ∧
      μ.map tr ≠ studentLaw (n-2)) ∧ ¬ LiteralCovarianceClaim := by
  have hh := corrected_residual_covariance_and_law μ Z x γ ε σ hZ h1 hx hn hi hij he hc
  dsimp only at hh ⊢
  exact ⟨hh.1,hh.2.1,hh.2.2.1,(hh.2.2.2.1 hσ).1,(hh.2.2.2.1 hσ).2,
    hh.2.2.2.2,zero_noise_refutes_literal_covariance⟩

/-- Full T7(i) quantifier order: regressor geometry holds before choosing any outcome. -/
theorem nested_standard_error_bound {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q : Fin n → ℝ)
    (hspan : ∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b)
    (h₁ : FullColumnRank (fullDesign Z₁ q))
    (h₂ : FullColumnRank (fullDesign Z₂ q))
    (hn₁ : k₁+1 < n) (hn₂ : k₂+1 < n) :
    let R₁ := olsSSE Z₁ q
    let R₂ := olsSSE Z₂ q
    (∃ a, IsLeastSquares Z₁ q a ∧ squaredLength (q-Z₁ *ᵥ a) = R₁) ∧
    (∃ a, IsLeastSquares Z₂ q a ∧ squaredLength (q-Z₂ *ᵥ a) = R₂) ∧
    0 < R₁ ∧ 0 < R₂ ∧ R₂ ≤ R₁ ∧
    ((fullDesign Z₁ q)ᵀ * fullDesign Z₁ q)⁻¹ (Fin.last k₁) (Fin.last k₁) = 1/R₁ ∧
    ((fullDesign Z₂ q)ᵀ * fullDesign Z₂ q)⁻¹ (Fin.last k₂) (Fin.last k₂) = 1/R₂ ∧
    (∀ y, 0 < olsSSE (fullDesign Z₁ q) y → 0 < olsSSE (fullDesign Z₂ q) y →
      let s₁ := Real.sqrt (olsSSE (fullDesign Z₁ q) y / ((n : ℝ)-k₁-1))
      let s₂ := Real.sqrt (olsSSE (fullDesign Z₂ q) y / ((n : ℝ)-k₂-1))
      let se₁ := Real.sqrt (olsSESquared (fullDesign Z₁ q) y (Fin.last k₁))
      let se₂ := Real.sqrt (olsSESquared (fullDesign Z₂ q) y (Fin.last k₂))
      se₁ = s₁ / Real.sqrt R₁ ∧ se₂ = s₂ / Real.sqrt R₂ ∧
      se₁/s₁ ≤ se₂/s₂ ∧ se₁ ≤ se₂*s₁/s₂) := by
  exact nested_standard_error_bound_full Z₁ Z₂ q hspan h₁ h₂ hn₁ hn₂

end
end AronowAudit.P039.PaperDomains
