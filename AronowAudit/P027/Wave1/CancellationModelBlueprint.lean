import AronowAudit.P027.Wave1.GaussianMomentsBlueprint

/-! # Blueprint: refutation of `AronowAudit.P027.cancellation_model_reading` (P027-T7, R1)

Dossier group P027, record 11. The frozen contract (source
`AronowAudit/P027/P027_Audit.lean`, `cancellation_model_reading`, a `sorry` draft) is the
explicitly labelled R1 reading of supplement p. A4: under the calibrated Gaussian
generator with plotted `r ∈ {2,10}`, `m ∈ {2,30,60}`, the demeaned periodic
populations have `A = 0` almost surely. Resolution `refute` (map-P027, accepted by
both referees without fixes).

Paper proof (map-P027 report, record 11): take `r = m = 2`, `ρ = 99/100`, the
eight-coordinate product of `N(0, 1791/100)` laws with coordinate errors, and
`β = (15/2) ρ √(7/8)`, which satisfies the exact calibration. Every hypothesis of
the contract holds. The actual expected bias is `E[A] = -q L` with
`L = 16 m² β² + m σ² (1 - 1/q) > 0` (existing proved `periodic_model_bias`), here
`-311418/25`, so `A` is not almost everywhere zero.

The frozen target is the negation of the exact recorded contract. The final
declaration (writer) is `AronowAudit.P027.Wave1.cancellation_model_counterexample`
in `AronowAudit/P027/Wave1/CancellationModel.lean`. Never use the false draft
`cancellation_model_reading` as a premise.
-/

namespace AronowAudit.P027.Wave1.CancellationModel

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Frozen target: the negation of the exact recorded contract of
`AronowAudit.P027.cancellation_model_reading` (all binders as in the source). -/
def Target : Prop :=
  ¬ (∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (r m : ℕ) (hr : 0 < r), 0 < m →
      r = 2 ∨ r = 10 → m = 2 ∨ m = 30 ∨ m = 60 →
      ∀ (ρ β : ℝ), |ρ| ≤ 1 →
      ∀ (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ),
      GaussianNoise μ ε (900*(1-ρ^2)) →
      β^2 = 900*ρ^2*((m:ℝ)*(2*r)-1)/(16*((m:ℝ)*(2*r))) →
      ∀ᵐ ξ ∂μ, biasA (phaseOriginal r m hr) (centeredOutcomes phaseSize β ε ξ) = 0)

/-- Fidelity check: `Target` is literally the negation of the frozen contract. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P027.cancellation_model_reading) := Iff.rfl

/-- N1 (shared node; map-P027 "Gaussian noise implies the stated moments"): proved
once as `AronowAudit.P027.Wave1.gaussian_noise_moments`. -/
def N1 : Prop := GaussianMoments.Target

/-- N2 (paper-proof step "μ is the product over K of the real Gaussian law
N(0,1791/100) and ε_k(ξ) = ξ_k; coordinate evaluation is measurable, has that
marginal law, and the coordinate family is independent"), for every finite
coordinate type and every real `σ2`. -/
def N2 : Prop :=
  ∀ {K : Type} [Fintype K] (σ2 : ℝ),
    GaussianNoise (Measure.pi (fun _ : K => gaussianReal 0 σ2.toNNReal))
      (fun k (ξ : K → ℝ) => ξ k) σ2

/-- The eight units `((i,b),j)` with `i,b,j ∈ Fin 2`. -/
abbrev K8 : Type := Σ _ : Fin 2 × Fin 2, Fin 2

/-- The witness variance `900 (1 - ρ²)` at `ρ = 99/100`, i.e. `1791/100`. -/
def witnessVar : ℝ := 900*(1-(99/100 : ℝ)^2)

/-- The witness slope `β = (15/2) ρ √(7/8)` at `ρ = 99/100`. -/
def witnessBeta : ℝ := (15/2 : ℝ) * (99/100) * Real.sqrt (7/8)

/-- The nodes suffice. The contract applied to the explicit product witness gives
`A = 0` a.e., hence `∫ A = 0`; the existing proved `periodic_model_bias` (with the
moment conditions from N1) gives `∫ A = -q L < 0`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro hcon
  have hσ : 0 < witnessVar := by norm_num [witnessVar]
  have hg : GaussianNoise (Measure.pi (fun _ : K8 => gaussianReal 0 witnessVar.toNNReal))
      (fun k (ξ : K8 → ℝ) => ξ k) witnessVar := h2 witnessVar
  have hβ : witnessBeta^2 =
      900*(99/100 : ℝ)^2*(((2:ℕ):ℝ)*(2*((2:ℕ):ℝ))-1)/(16*(((2:ℕ):ℝ)*(2*((2:ℕ):ℝ)))) := by
    rw [witnessBeta, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hae := hcon (Measure.pi (fun _ : K8 => gaussianReal 0 witnessVar.toNNReal)) 2 2
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl) (99/100) witnessBeta
    (by rw [abs_le]; constructor <;> norm_num) (fun k ξ => ξ k) hg hβ
  have hnm := h1 (Measure.pi (fun _ : K8 => gaussianReal 0 witnessVar.toNNReal))
    (fun k (ξ : K8 → ℝ) => ξ k) witnessVar hσ.le hg
  have hb := periodic_model_bias (Measure.pi (fun _ : K8 => gaussianReal 0 witnessVar.toNNReal))
    2 2 (by norm_num) (by norm_num) witnessBeta witnessVar (fun k ξ => ξ k) hnm
  dsimp only at hb
  obtain ⟨-, -, hA, -⟩ := hb
  have h0 : outcomeE (Measure.pi (fun _ : K8 => gaussianReal 0 witnessVar.toNNReal))
      (fun ξ => biasA (phaseOriginal 2 2 (by norm_num))
        (centeredOutcomes phaseSize witnessBeta (fun k ξ => ξ k) ξ)) = 0 := by
    unfold outcomeE
    rw [integral_congr_ae hae]
    simp
  rw [h0] at hA
  have hL : 0 < 16*((2:ℕ):ℝ)^2*witnessBeta^2 +
      ((2:ℕ):ℝ)*witnessVar*(1-1/(2*((2:ℕ):ℝ))) := by
    have := sq_nonneg witnessBeta
    norm_num
    nlinarith
  have hq : (0:ℝ) < 2*((2:ℕ):ℝ) := by norm_num
  nlinarith

end
end AronowAudit.P027.Wave1.CancellationModel
