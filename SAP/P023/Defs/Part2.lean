import SAP.P023.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! Election designs, population laws, and estimator definitions. -/

def supError (h : ℝ → ℝ) (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x => |h x - p.eval x|) '' Set.Icc (-1) 1)

def rmsError (μ : Measure ℝ) (h : ℝ → ℝ) (p : Polynomial ℝ) : ℝ :=
  Real.sqrt (expectation μ (fun x => (h x - p.eval x)^2))

def ConditionalMean (ν : Measure (ℝ × ℝ)) (m : ℝ → ℝ) : Prop :=
  Integrable (fun z => z.2) ν ∧ Integrable (fun z => m z.1) ν ∧
  ∀ t : ℝ → ℝ, Measurable t → (∃ B, ∀ x, |t x| ≤ B) →
    (∫ z, t z.1 * z.2 ∂ν) = ∫ z, t z.1 * m z.1 ∂ν

def marginLaw (ν : Measure (ℝ × ℝ)) : Measure ℝ := Measure.map Prod.fst ν

def noiseLaw : Measure ℝ := (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 / 10) +
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 / 10)

def witnessLaw (μ : Measure ℝ) (h : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun z : ℝ × ℝ => (z.1, 1 / 2 + h z.1 + z.2)) (μ.prod noiseLaw)

def sigmoid (a η x : ℝ) : ℝ := a * max (-1) (min 1 (x / η))

def triangular (c w x : ℝ) : ℝ := max (w - |x - c|) 0 / w^2

def clusterDensity (d x : ℝ) : ℝ := d^4 / 2 +
  (1 - d^4) / 2 * (triangular (1 / 2) (d / 2) x + triangular (-1 / 2) (d / 2) x)

def clusteredMargins (d : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Icc (-1) 1)).withDensity (fun x => ENNReal.ofReal (clusterDensity d x))

def clusterPositive (d x : ℝ) : ℝ :=
  if x < 1 / 2 - d then 0 else if x ≤ 1 / 2 - d / 2 then 1 / 2 - d - x
  else if x ≤ 1 / 2 + d / 2 then x - 1 / 2
  else if x ≤ 1 / 2 + d then 1 / 2 + d - x else 0

def clusterSmooth (d x : ℝ) : ℝ := if x < 0 then -clusterPositive d (-x) else clusterPositive d x

def projection1 (x : ℝ) : ℝ := 1 / 2 + 3 / 4 * x

def projection7 (x : ℝ) : ℝ := 1 / 2 +
  (11025*x - 40425*x^3 + 63063*x^5 - 32175*x^7) / 4096

def centralBinomial (n : ℕ) : ℝ := (Nat.choose (2*n) n : ℝ) / 4^n

def appendixSmooth (g f : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  if x < 0 then g x - α else f x - (α + β)

def appendixMean (g f : ℝ → ℝ) (x : ℝ) : ℝ := if x < 0 then g x else f x

def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ℝ) (z : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun N => P {ω | ε < |Z N ω - z|}) atTop (nhds 0)

def IIDSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ) : Prop :=
  ProbabilityLaw P ∧ (∀ i, Measurable (sample i)) ∧
  (∀ i, Measure.map (sample i) P = ν) ∧ ProbabilityTheory.iIndepFun sample P

def samplePolynomial {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (N J : ℕ) (ω : Ω) : ℝ :=
  polynomialOLS J (fun i : Fin N => (sample i ω).1)
    (fun i : Fin N => party (sample i ω).1) (fun i : Fin N => (sample i ω).2)

def sampleRD {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (k : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  rd (k N) (fun i : Fin N => (sample i ω).1)
    (fun i : Fin N => party (sample i ω).1) (fun i : Fin N => (sample i ω).2)

def RepairedRegularity (ν : Measure (ℝ × ℝ)) (α β : ℝ) (h : ℝ → ℝ)
    (c δ L σ2 : ℝ) : Prop :=
  ProbabilityLaw ν ∧ MarginSupport (marginLaw ν) ∧ marginLaw ν {0} = 0 ∧
  Integrable (fun z => z.2^2) ν ∧ 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ σ2 ∧
  (∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
    ENNReal.ofReal c * volume A ≤ marginLaw ν A) ∧
  h 0 = 0 ∧ (∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1, |h x - h x'| ≤ L * |x-x'|) ∧
  ConditionalMean ν (fun x => α + β*party x + h x) ∧
  (∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
    (∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2 - (α + β*party z.1 + h z.1))^2 ∂ν) ≤
      σ2 * (marginLaw ν A).toReal)

def jacksonK : ℝ := 3 * (1 + Real.pi^4) / (4 * Real.pi)

def smallestMomentEigenvalue (μ : Measure ℝ) (J : ℕ) : ℝ :=
  sInf {r | ∃ a : Fin (J+2) → ℝ, (∑ j, a j^2) = 1 ∧
    r = expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) a x ^ 2)}

def UsualRDRegularity (ν : Measure (ℝ × ℝ)) (m : ℝ → ℝ) (k : ℕ → ℝ) : Prop :=
  marginLaw ν {0} = 0 ∧
  Tendsto (fun N : ℕ => (N:ℝ)*(marginLaw ν (Set.Ioc 0 (k N))).toReal) atTop atTop ∧
  Tendsto (fun N : ℕ => (N:ℝ)*(marginLaw ν (Set.Ioo (-k N) 0)).toReal) atTop atTop ∧
  ∃ δ σ2 : ℝ, 0 < δ ∧ 0 ≤ σ2 ∧
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
      (∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2-m z.1)^2 ∂ν) ≤ σ2*(marginLaw ν A).toReal

def coarsenedWeight (k : ℝ) (x d : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if i ∈ close k x then d i / (∑ l ∈ close k x, d l) -
    (1-d i) / (∑ l ∈ close k x, (1-d l)) else 0

def smoothDesign (J : ℕ) (x : ι → ℝ) : ι → Fin (J+1) → ℝ := fun i j => x i ^ j.val

def finiteResidual (J : ℕ) (x d : ι → ℝ) (i : ι) : ℝ :=
  d i - predict (smoothDesign J x) (olsCoefficients (smoothDesign J x) d) i

def finiteWeight (J : ℕ) (x d : ι → ℝ) (i : ι) : ℝ :=
  finiteResidual J x d i / dot (finiteResidual J x d) (finiteResidual J x d)

def binSet {η : Type*} [DecidableEq η] (B : ι → η) (j : η) : Finset ι :=
  Finset.univ.filter (fun i => B i = j)

def binMean {η : Type*} [DecidableEq η] (B : ι → η) (j : η) (z : ι → ℝ) : ℝ :=
  (∑ i ∈ binSet B j, z i) / (binSet B j).card

def demeaned {η : Type*} [DecidableEq η] (B : ι → η) (z : ι → ℝ) (i : ι) : ℝ :=
  z i - binMean B (B i) z

def predictionRisk (ν : Measure (ℝ × ℝ)) (f : ℝ → ℝ) : ℝ :=
  ∫ z, (z.2-f z.1)^2 ∂ν

def fittedRisk (ν : Measure (ℝ × ℝ)) (J : ℕ) : ℝ :=
  sInf {e | ∃ c : Fin (J+2) → ℝ,
    e = predictionRisk ν (predict (polynomialDesign J (fun x : ℝ => x) party) c)}

/-- Singular sample designs have probability tending to zero. -/
def OLSAdmissible {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (sample : ℕ → Ω → ℝ × ℝ) (degrees : ℕ → ℕ) : Prop :=
  Tendsto (fun N => P {ω | ¬ FullRank (polynomialDesign (degrees N)
    (fun i : Fin N => (sample i ω).1)
    (fun i : Fin N => party (sample i ω).1))}) atTop (nhds 0)

/-- The probability of an empty winner or loser window tends to zero. -/
def RDAdmissible {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (sample : ℕ → Ω → ℝ × ℝ) (k : ℕ → ℝ) : Prop :=
  Tendsto (fun N => P {ω | ¬ (
    0 < ∑ i ∈ close (k N) (fun i : Fin N => (sample i ω).1), party (sample i ω).1 ∧
    0 < ∑ i ∈ close (k N) (fun i : Fin N => (sample i ω).1), (1-party (sample i ω).1))})
    atTop (nhds 0)
end
end SAP.P023
