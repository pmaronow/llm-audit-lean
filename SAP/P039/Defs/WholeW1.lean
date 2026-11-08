import Mathlib
import SAP.P039.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal ENNReal
open MeasureTheory ProbabilityTheory

/-- The actual two-sided probability under the product-Gaussian Student reference law.
The whole statements use this only at positive degrees of freedom. -/
noncomputable def studentTailProbability (ν : ℕ) (t : ℝ) : ℝ :=
  ((studentLaw ν) {s : ℝ | t ≤ |s|}).toReal

/-- The normal/chi-square mixture density, written as a nonnegative integral so that
no Bochner integral is silently totalized. Used only for `0 < ν`. -/
noncomputable def studentMixtureDensity (ν : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ w : ℝ, ENNReal.ofReal
    (Real.sqrt (w / ν) * gaussianPDFReal 0 1 (Real.sqrt (w / ν) * t))
      ∂gammaMeasure ((ν : ℝ) / 2) (1 / 2)

/-- The usual Student density, used only for positive integer degrees of freedom. -/
noncomputable def wholeStudentDensity (ν : ℕ) (t : ℝ) : ℝ :=
  Real.Gamma (((ν : ℝ) + 1) / 2) /
    (Real.sqrt ((ν : ℝ) * Real.pi) * Real.Gamma ((ν : ℝ) / 2)) *
      (1 + t ^ 2 / ν) ^ (-(((ν : ℝ) + 1) / 2))

/-- The intermediate comparisons printed in T3(iii). -/
def WitnessTailComparisons : Prop :=
  (900 : ℝ) ^ 2 = 810000 ∧ (247 : ℝ) ^ 2 * 13 = 793117 ∧
  (793117 : ℝ) < 810000 ∧ 247 * Real.sqrt (13 : ℝ) < 900 ∧
  (3 * Real.sqrt (3 : ℝ) / 2) / Real.sqrt 3 = 3 / 2 ∧
  Real.arctan (3 / 2 : ℝ) = Real.pi / 4 + Real.arctan (1 / 5) ∧
  Real.arctan (1 / 5 : ℝ) < 1 / 5 ∧ (3 : ℝ) < Real.pi ∧
  1 / 2 - (2 / 3 : ℝ) * (1 / 5 + 6 / 13) = 23 / 390 ∧
  (23 / 390 : ℝ) < studentThreeTail (3 * Real.sqrt 3 / 2) ∧
  (1 / 20 : ℝ) < 23 / 390

/-- P039-T3; Figure 4 and p. 138, compared with Table 2, p. 137 and Table 3, p. 139.
The six-observation OLS witnesses give different tests at 5%, different slopes for
the correlated regressor, and the stated Gaussian-null scaled-t3 law and moments.
For every nonnegative threshold the two analytic formulas are the actual t4 and
t3 two-sided probability tails. The intermediate square and arctangent comparisons
and four-decimal p-value enclosures hold. The usual measure-theoretic conditions
are assumed; statistics are totalized on the Gaussian null set of zero SSE. -/
def T3WholeStatement : Prop :=
  T3Statement ∧
  (olsResidual witnessZ witnessY = (3 / 2 : ℝ) • witnessV + witnessW) ∧
  (∀ t : ℝ, 0 ≤ t →
    studentTailProbability 4 t = studentFourTail t ∧
    studentTailProbability 3 t = studentThreeTail t) ∧
  WitnessTailComparisons ∧
  (studentTailProbability 4 3 = 1 - 45 / (13 * Real.sqrt 13) ∧
    studentTailProbability 4 3 < 1 / 20 ∧
    studentTailProbability 3 (3 * Real.sqrt 3 / 2) =
      1 / 2 - 2 / Real.pi * (Real.arctan (1 / 5) + 6 / 13) ∧
    (23 / 390 : ℝ) < studentTailProbability 3 (3 * Real.sqrt 3 / 2)) ∧
  ((0.03985 : ℝ) ≤ studentTailProbability 4 3 ∧
    studentTailProbability 4 3 < 0.03995 ∧
    (0.08045 : ℝ) ≤ studentTailProbability 3 (3 * Real.sqrt 3 / 2) ∧
    studentTailProbability 3 (3 * Real.sqrt 3 / 2) < 0.08055)

/-- The unit contrast of the additional regressor after removing the controls. -/
noncomputable def wholeRegressorContrast {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (Real.sqrt (dotProduct x (residualMaker Z *ᵥ x)))⁻¹ • (residualMaker Z *ᵥ x)

/-- Geometry and coefficient identities used to build orthonormal Gaussian coordinates.
No intercept assumption is needed for this auxiliary predicate. -/
def WholeRegressionGeometry {n k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) : Prop :=
  let sm := dotProduct x (residualMaker Z *ᵥ x)
  let e := wholeRegressorContrast Z x
  let Q := residualMaker (fullDesign Z x)
  0 < sm ∧ dotProduct e e = 1 ∧ Qᵀ = Q ∧ Q * Q = Q ∧
  Q *ᵥ e = 0 ∧ Q.rank = n - k - 1 ∧
  (∀ (γ : Fin k → ℝ) (ε : Fin n → ℝ),
    ols (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k) * Real.sqrt sm =
      dotProduct e ε) ∧
  (∀ (γ : Fin k → ℝ) (ε : Fin n → ℝ),
    olsResidual (fullDesign Z x) (Z *ᵥ γ + ε) = Q *ᵥ ε) ∧
  (∀ y : Fin n → ℝ, olsSESquared (fullDesign Z x) y (Fin.last k) =
    olsSSE (fullDesign Z x) y / (((n : ℝ) - k - 1) * sm))

/-- An orthonormal row frame whose first coordinate is a specified contrast and
whose remaining squared coordinates give the projection energy. -/
def WholeProjectionFrame {n ν : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → ℝ) (B : Matrix (Fin (ν + 1)) (Fin n) ℝ) : Prop :=
  B * Bᵀ = 1 ∧ (∀ j, B 0 j = e j) ∧
  ∀ z : Fin n → ℝ,
    squaredLength (Q *ᵥ z) = ∑ i : Fin ν, ((B *ᵥ z) i.succ) ^ 2

/-- Gaussian clause of T4(f), with no Student-law premise. A positive NNReal scale
ranges over exactly all positive real scales. The explicit pushforward is the
centered joint Gaussian law with covariance sigma squared times the identity. -/
def WholeGaussianRegressionStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n k : ℕ} (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ)
    (γ : Fin k → ℝ) (ε : Ω → Fin n → ℝ) (σ : ℝ≥0),
    0 < σ → FullColumnRank Z → (∃ c, Z *ᵥ c = fun _ => 1) →
    (¬ ∃ c, Z *ᵥ c = x) → k + 1 < n → Measurable ε →
    μ.map ε = Measure.pi (fun _ : Fin n => gaussianReal 0 (σ ^ 2)) →
    let Y := fun ω => Z *ᵥ γ + ε ω
    let tf := fun ω => olsT (fullDesign Z x) (Y ω) (Fin.last k)
    let tr := fun ω => olsT (residualLine x) (residualMaker Z *ᵥ Y ω) 1
    μ.map tf = studentLaw (n - k - 1) ∧
    (∀ᵐ ω ∂μ, 0 < olsSSE (fullDesign Z x) (Y ω)) ∧
    (∀ᵐ ω ∂μ, 0 < olsSSE (residualLine x) (residualMaker Z *ᵥ Y ω)) ∧
    (controlProjection Z *ᵥ (x - ((∑ i, x i) / (n : ℝ)) • (fun _ => 1)) = 0 →
      μ.map tr = (studentLaw (n - k - 1)).map
        (fun t => Real.sqrt (((n : ℝ) - 2) / ((n : ℝ) - k - 1)) * t) ∧
      (2 ≤ k → μ.map tr ≠ studentLaw (n - 2)))

/-- P039-T4; p. 138, final sentence, with the exact linear-OLS interpretation.
For every full-rank control design containing an intercept and every additional
regressor outside its span, clauses (a)--(e) give the projection, attenuation,
SE and t identities. Under positive isotropic noise the residual covariance has
rank n-k. Under the Gaussian null the full statistic has the central t(n-k-1)
law; an orthogonal centered regressor gives the stated scaled residual-line law,
which differs from t(n-2) when k is at least two, including residual df one or two.
The usual measure-theoretic conditions are assumed. The empirical nonlinear
application in (g) is expressly outside the formal claim. -/
def T4WholeStatement : Prop :=
  T4Statement ∧ WholeGaussianRegressionStatement

/-- RMSQ under the alternative convention, used below only at sample size 17. -/
noncomputable def wholeRMSQ {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) : ℝ := Real.sqrt (olsSSE A y / n)

/-- The alternative RMSQ reading in T7(ii), including the stronger numerical bound
and the contradiction from the four closed rounding bins. -/
def AlternativeRMSQStatement : Prop :=
  0 < Real.sqrt (13 / 14 : ℝ) ∧ Real.sqrt (13 / 14 : ℝ) < 1 ∧
  (7141 / 7512 : ℝ) * Real.sqrt (13 / 14 : ℝ) < 7141 / 7512 ∧
  ∀ (Z₁ : Matrix (Fin 17) (Fin 2) ℝ) (Z₂ : Matrix (Fin 17) (Fin 3) ℝ)
    (q y : Fin 17 → ℝ),
    (∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b) →
    FullColumnRank (fullDesign Z₁ q) → FullColumnRank (fullDesign Z₂ q) →
    let A₁ := fullDesign Z₁ q
    let A₂ := fullDesign Z₂ q
    let m₁ := wholeRMSQ A₁ y
    let m₂ := wholeRMSQ A₂ y
    let se₁ := Real.sqrt (olsSESquared A₁ y 2)
    let se₂ := Real.sqrt (olsSESquared A₂ y 3)
    (0 < olsSSE A₁ y → 0 < olsSSE A₂ y →
      olsResidualStandardError A₁ y / olsResidualStandardError A₂ y =
        Real.sqrt (13 / 14 : ℝ) * (m₁ / m₂) ∧
      (se₂ ≤ 0.965 → m₁ ≤ 4.625 → 4.695 ≤ m₂ →
        se₁ ≤ (7141 / 7512 : ℝ) * Real.sqrt (13 / 14 : ℝ))) ∧
    (se₁ ∈ Set.Icc (1.35 : ℝ) 1.45 → se₂ ∈ Set.Icc (0.955 : ℝ) 0.965 →
      m₁ ∈ Set.Icc (4.615 : ℝ) 4.625 → m₂ ∈ Set.Icc (4.695 : ℝ) 4.705 → False)

/-- P039-T7; Table 2, p. 137, and the specifications on p. 136.
Nested OLS gives the inverse-Gram and SE inequalities, the exact printed-cell
bound and positive gap, and incompatibility of all four printed rounding bins.
The alternative RMSQ convention sqrt(SSE/17) multiplies the ratio bound by
sqrt(13/14), strictly reducing it. The exact deposited inputs give the unique
corrected fits, income coefficients and SE displays .94, .96 and 1.0 (or 1.01).
All three corrected income coefficients retain their stars: their actual
two-sided Student reference probabilities, on 14, 13 and 12 df, are below .01.
The usual measure-theoretic conditions are assumed. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ AlternativeRMSQStatement ∧
  studentTailProbability 14 |olsT tableA1 tableTwoOutcome 1| < 1 / 100 ∧
  studentTailProbability 13 |olsT tableA2 tableTwoOutcome 1| < 1 / 100 ∧
  studentTailProbability 12 |olsT tableA3 tableTwoOutcome 1| < 1 / 100

end SAP.P039
