import Mathlib
import SAP.P015b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b

universe u v w z

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

/-- Conditional independence, expressed by conditional probabilities of all pairs
of measurable events. This definition applies to an arbitrary ambient probability
space; it is the event-factorization definition used by `AronowAudit.P001.CI`. -/
def WholeConditionalIndependent {Ω : Type u} {E : Type v} {F : Type w} {G : Type z}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (P : Measure Ω) (X : Ω → E) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    P[(Y ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P]
    fun s => P[(Y ⁻¹' A).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance] s *
      P[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance] s

/-- The population identities used twice in the proof of corrected (7).
All conditional equalities are almost sure. The residual-product factorization
is displayed separately from its zero value. -/
def WholeMomentIdentities {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ) (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ) (ω : Fin (K+1) → ℝ) : Prop :=
  let m := fun s => dotProduct (controlVector (X s)) ω
  let r := fun s => D s - m s
  let C := MeasurableSpace.comap X inferInstance
  (P[(fun s => D s * Y₀ s) | C] =ᵐ[P] fun s => P[D | C] s * P[Y₀ | C] s) ∧
  (P[r | C] =ᵐ[P] fun _ => 0) ∧
  (P[(fun s => r s * τ s) | C] =ᵐ[P] fun s => P[r | C] s * P[τ | C] s) ∧
  (P[(fun s => r s * τ s) | C] =ᵐ[P] fun _ => 0) ∧
  ((∫ s, D s * Y₀ s ∂P) - (∫ s, m s * Y₀ s ∂P) = 0) ∧
  (∫ s, r s * m s * τ s ∂P) = 0

/-- The sufficient reading of A.1(4) is the existing eight-family
`RegressionRegularity`. It supplies all the integrability needed below. -/
def WholeRegularityMoments : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (_hD : Measurable (D 0)) (_hY : Measurable (Y₀ 0))
    (_hτ : Measurable (τ 0)) (_hX : Measurable (X 0))
    (_hunconf : WholeConditionalIndependent P (X 0) (fun s => (Y₀ 0 s, τ 0 s)) (D 0))
    (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (_hreg : RegressionRegularity P D Y₀ τ X),
    WholeMomentIdentities P K (D 0) (Y₀ 0) (τ 0) (X 0) ω

/-- The actual inverse-formula OLS coefficient, completed by the matrix inverse
on singular samples, converges in probability on every ambient probability
space. The eight moment families ensure that the numerator is integrable;
positive finite mean weight is part of `RegressionRegularity`. -/
def WholeCausalOLSConvergence : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (_hD : ∀ i, Measurable (D i)) (_hY : ∀ i, Measurable (Y₀ i))
    (_hτ : ∀ i, Measurable (τ i)) (_hX : ∀ i, Measurable (X i))
    (_hiid : iIndepFun (fun i s => (D i s, Y₀ i s, τ i s, X i s)) P)
    (_hident : ∀ i, IdentDistrib (fun s => (D i s, Y₀ i s, τ i s, X i s))
      (fun s => (D 0 s, Y₀ 0 s, τ 0 s, X 0 s)) P P)
    (_hunconf : WholeConditionalIndependent P (X 0) (fun s => (Y₀ 0 s, τ 0 s)) (D 0))
    (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (_hreg : RegressionRegularity P D Y₀ τ X),
    Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s * τ 0 s) P ∧
    TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => (∫ s, squaredPopulationResidual P (D 0) (X 0) s * τ 0 s ∂P) /
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P))

/-- The corrected coefficient column has exactly K+2 entries. For an affine
potential-outcome surface, its observed-data inverse formula has the same
treatment coordinate as `treatmentEstimate`. -/
def WholeCoefficientFormula : Prop :=
  ∀ {Ω : Type u} (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ → ℝ)
    (_hpot : ∀ i s d, Y i s d = Y₀ i s + τ i s * d) (n : ℕ) (s : Ω),
    let W := regressionDesign D X n s
    let y : Fin n → ℝ := fun i => Y i s (D i s)
    let θ : Fin (K+2) → ℝ := sampleCoefficients W y
    θ = (W.transpose * W)⁻¹.mulVec (W.transpose.mulVec y) ∧
      θ 1 = treatmentEstimate D Y₀ τ X n s

/-- A two-atom confounding witness to the insufficiency of (1) and (3) alone:
D=Y(0)=tau is a fair bit, with no controls and mean treatment 1/2. Both
factorizations fail, and the population slope is 2 while the weighted effect
is 1/2. The potential outcomes are Y(d)=D+D*d. -/
def WholeConfoundingWitness : Prop :=
  let p : Fin 2 → ℝ := fun _ => 1/2
  let D : Fin 2 → ℝ := fun i => (i : ℕ)
  let X : Fin 2 → Unit := fun _ => ()
  let r : Fin 2 → ℝ := fun i => D i - 1/2
  IsFiniteLaw p ∧
  (∀ i d, linearOutcome (D i) (D i) d = D i + D i * d) ∧
  (∀ i, finiteCellMean p X D (X i) = 1/2) ∧
  finiteMean p (fun i => D i * D i) = 1/2 ∧
  finiteMean p D * finiteMean p D = 1/4 ∧
  (∀ i, finiteCellMean p X (fun a => r a * D a) (X i) = 1/4) ∧
  (∀ i, finiteCellMean p X r (X i) * finiteCellMean p X D (X i) = 0) ∧
  ¬ finiteUnconfounded p X (fun i => (D i, D i)) D ∧
  populationCoefficients p (fun i => ![1, D i])
    (fun i => linearOutcome (D i) (D i) (D i)) 1 = 2 ∧
  finiteMean p (fun i => r i ^ 2) = 1/4 ∧
  finiteMean p (fun i => r i ^ 2 * D i) / finiteMean p (fun i => r i ^ 2) = 1/2

/-- P015-T15; p. 254 (PDF p. 5), corrected expression (7); Appendix A,
p. 262 (PDF p. 13).
Under unconfoundedness, affine potential outcomes, the linear conditional
treatment mean, and the stated eight-family regularity, the actual OLS
treatment coefficient converges in probability to E[w tau]/E[w], with
w=(D-E[D|X])^2, on any ambient probability space. The two conditional
factorizations and their zero-moment consequences hold; the corrected OLS
coefficient column has K+2 coordinates. A fair-bit confounding example shows
that conditions (1) and (3) alone do not imply the factorizations. -/
def T15WholeStatement : Prop :=
  WholeCausalOLSConvergence.{u} ∧ WholeRegularityMoments.{u} ∧
    WholeCoefficientFormula.{u} ∧ WholeConfoundingWitness

/-- P015-T22; p. 262 (PDF p. 13), Theorem A.1; proof pp. 262-263
(PDF pp. 13-14); expression (7), p. 254 (PDF p. 5).
For measurable iid unit data on any probability space, unconfoundedness,
affine potential outcomes, a linear conditional treatment mean, and the
stated eight-family regularity imply convergence in probability of the actual
OLS treatment coefficient to E[w tau]/E[w], where w=(D-E[D|X])^2. The
numerator is integrable and the denominator has positive finite expectation.
The inverse formula completes the estimator on singular finite samples. -/
def T22WholeStatement : Prop := WholeCausalOLSConvergence.{u}

end
end SAP.P015b
