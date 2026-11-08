import Mathlib
import SAP.P001a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a

def expectedLogLikelihood {Ω : Type*} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ :=
  mean μ (fun ω => Real.log (g (Y ω) (X ω) t))

def sampleLogLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  sampleMean (fun i ω => Real.log (g (Y i ω) (X i ω) t)) n ω

def mixtureFamily {M K τ : ℕ} (p : (Fin τ → ℝ) → Fin M → ℝ)
    (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∑ m,p t m*g m y x t

def finiteSampleMean {n : ℕ} (X : Fin n → ℝ) : ℝ := (∑ i,X i)/(n : ℝ)

def covarianceMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (X : Ω → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => covariance (fun ω => X ω j) (fun ω => X ω k) μ

def modelScore {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : Fin τ → ℝ :=
  fun j => fderiv ℝ (fun u => Real.log (g y x u)) t (Pi.single j 1)

def modelHessian {K τ : ℕ}
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (y : ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => fderiv ℝ (fun u => modelScore g y x u j) t (Pi.single k 1)

def informationMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => mean μ (fun ω => modelScore g (Y ω) (X ω) t j*modelScore g (Y ω) (X ω) t k)

def populationHessian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => mean μ (fun ω => modelHessian g (Y ω) (X ω) t j k)

def sampleHessian {Ω : Type*} {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : Matrix (Fin τ) (Fin τ) ℝ :=
  fun j k => (∑ i∈Finset.range n,modelHessian g (Y i ω) (X i ω) t j k)/(n : ℝ)

def normalVectorLaw {τ : ℕ} (S : Matrix (Fin τ) (Fin τ) ℝ) : Measure (Fin τ → ℝ) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin τ)) S).map (fun z => fun j => z j)

def estimatedMatchIntercept {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  clip (1/8) (3/8) ((∑ i,((if (s i).2.1 then (1 : ℝ) else 0)-((s i).1-1/4)))/(n : ℝ))

def estimatedMatchScore {n : ℕ} (s : Fin n → ℝ × Bool × Bool) (i : Fin n) : ℝ :=
  estimatedMatchIntercept s+((s i).1-1/4)

def causalMatchEstimated {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  causalMatch (fun i => (estimatedMatchScore s i,(s i).2))

def donorReuseWeight {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (j : Fin n) : ℝ :=
  if r j then 1+((Finset.univ.filter (fun i => r i=false ∧ nearestDonor p r i=some j)).card : ℝ) else 0

def signProductLaw (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n =>
    (1/2 : ℝ≥0∞) • Measure.dirac true+(1/2 : ℝ≥0∞) • Measure.dirac false)

def disjointMixtureParameterSet : Set (Fin 3 → ℝ) :=
  Set.Icc (![0,0,1/4]) (![1,1,3/4])

def disjointMixtureLikelihood {n : ℕ} (y : Fin n → Fin 4) (t : Fin 3 → ℝ) : ℝ :=
  ∏ i,disjointMixture (t 0) (t 1) (t 2) (y i)

def placeboRegressor (i : Fin 12) : Fin 3 → ℝ := ![1,placeboX i,placeboW i]

def placeboMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => fmean placeboLaw (fun i => placeboRegressor i j*placeboRegressor i k)

def placeboRisk (a b c : ℝ) : ℝ :=
  fmean placeboLaw (fun i => (placeboD i-a-b*placeboX i-c*placeboW i)^2)

def sampleLikelihood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) (t : Fin τ → ℝ) : ℝ :=
  ∏ i∈Finset.range n,g (Y i ω) (X i ω) t

def finiteMixtureSampleProb {n : ℕ} (t : Fin 3 → ℝ)
    (A : (Fin n → Fin 4) → Prop) : ℝ :=
  ∑ y : Fin n → Fin 4,if A y then disjointMixtureLikelihood y t else 0

def HasVectorPDF {K : ℕ} (ν : Measure (Fin K → ℝ)) (f : (Fin K → ℝ) → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
  ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

def FiniteMixtureConsistent
  (T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ) (θ : Fin 3 → ℝ) : Prop :=
  ∀ k : Fin 3, ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => finiteMixtureSampleProb θ (fun y => |T n y k-θ k| < ε))
    atTop (nhds 1)

def UnusedMixtureWitness : Prop :=
  IsCompact disjointMixtureParameterSet ∧
  (![1,1/3,1/4] : Fin 3 → ℝ) ∈ disjointMixtureParameterSet ∧
  (![1,1/3,3/4] : Fin 3 → ℝ) ∈ disjointMixtureParameterSet ∧
  disjointMixture 1 (1/3) (1/4) = ![2/3,1/3,0,0] ∧
  disjointMixture 1 (1/3) (3/4) = ![2/3,1/3,0,0] ∧
  (∀ n (y : Fin n → Fin 4), ∃ t ∈ disjointMixtureParameterSet,
    ∀ u ∈ disjointMixtureParameterSet, disjointMixtureLikelihood y u ≤
      disjointMixtureLikelihood y t) ∧
  (∀ n (T : (Fin n → Fin 4) → Fin 3 → ℝ),
    (∑ y : Fin n → Fin 4, disjointMixtureLikelihood y ![1,1/3,1/4]) = 1 ∧
    (∀ y : Fin n → Fin 4, 0 ≤ disjointMixtureLikelihood y ![1,1/3,1/4]) ∧
    (∀ y : Fin n → Fin 4, disjointMixtureLikelihood y ![1,1/3,1/4] =
      disjointMixtureLikelihood y ![1,1/3,3/4]) ∧
    finiteMixtureSampleProb (![1,1/3,1/4]) (fun y => |T y 2-1/4| < 1/8) +
      finiteMixtureSampleProb (![1,1/3,3/4]) (fun y => |T y 2-3/4| < 1/8) ≤ 1) ∧
  (∀ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    ¬ (FiniteMixtureConsistent T (![1,1/3,1/4]) ∧
       FiniteMixtureConsistent T (![1,1/3,3/4])))

def averageKLExt {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, InformationTheory.klDiv
    (κ.withDensity (fun y => ENNReal.ofReal (f y x)))
    (κ.withDensity (fun y => ENNReal.ofReal (g y x t))) ∂νX

def iidObservationLaw {E : Type*} [MeasurableSpace E] (ν : Measure E) (n : ℕ) :
    Measure (Fin n → E) := Measure.pi (fun _ : Fin n => ν)

def SampleCP {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : Measure E) (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (θ : Fin τ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => prob (iidObservationLaw ν n) {s | ε ≤ dist (T n s) θ}) atTop (nhds 0)

def SampleWeakLimit {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : ℕ → Measure E) (Z : (n : ℕ) → (Fin n → E) → Fin τ → ℝ)
    (γ : Measure (Fin τ → ℝ)) : Prop :=
  ∀ f : (Fin τ → ℝ) → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => mean (iidObservationLaw (ν n) n) (fun s => f (Z n s)))
      atTop (nhds (mean γ f))

def RegularAL {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : (Fin τ → ℝ) → Measure E) (θ : Fin τ → ℝ)
    (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (ψ : E → Fin τ → ℝ) : Prop :=
  (∀ n, Measurable (T n)) ∧ Measurable ψ ∧
  (∀ j, MemLp (fun z => ψ z j) 2 (ν θ)) ∧
  (∀ j, mean (ν θ) (fun z => ψ z j)=0) ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob (iidObservationLaw (ν θ) n)
    {s | ε ≤ dist (Real.sqrt n • (T n s-θ))
      ((Real.sqrt n)⁻¹ • (fun j => ∑ i, ψ (s i) j))}) atTop (nhds 0)) ∧
  (∀ h : Fin τ → ℝ, SampleWeakLimit (fun n => ν (θ+(Real.sqrt n)⁻¹ • h))
    (fun n s => Real.sqrt n • (T n s-(θ+(Real.sqrt n)⁻¹ • h)))
    (normalVectorLaw (covarianceMatrix (ν θ) ψ)))

def QuadraticMeanModel {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin τ → ℝ,
    dist t θ < δ →
    (∫ xy : (Fin K → ℝ) × ℝ,
      (Real.sqrt (g xy.2 xy.1 t)-Real.sqrt (g xy.2 xy.1 θ)-
       (∑ j, (t j-θ j)*modelScore g xy.2 xy.1 θ j)*
         Real.sqrt (g xy.2 xy.1 θ)/2)^2 ∂(νX.prod κ)) ≤ ε*(dist t θ)^2

def finiteLawMeasure {n : ℕ} (P : FiniteLaw n) : Measure (Fin n) :=
  ∑ i, ENNReal.ofReal (P.weight i) • Measure.dirac i

def placeboSampleF {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω) : ℝ :=
  placeboFStatistic (fun i : Fin n => fun _ : Fin 1 => placeboX (Z i.val ω))
    (fun i : Fin n => fun _ : Fin 1 => placeboW (Z i.val ω))
    (fun i : Fin n => placeboD (Z i.val ω))

def placeboSampleWald {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω) : ℝ :=
  let P : Matrix (Fin n) (Fin 3) ℝ := fun i =>
    ![1,placeboX (Z i.val ω),placeboW (Z i.val ω)]
  let D : Fin n → ℝ := fun i => placeboD (Z i.val ω)
  let β := olsCoef P D
  (β 2)^2/(robustCov P (D-P.mulVec β) 2 2)

def pda_at_mean_printed_contract : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ (X Y : Ω → ℝ), Measurable X → Measurable Y → Integrable X μ →
    ∀ (fX : ℝ → ℝ), HasPDF (μ.map X) fX →
    ∀ (m m' : ℝ → ℝ),
      IsCEF μ X Y m → IsCEF μ X Y m' →
      (∀ x, 0 < fX x → DifferentiableAt ℝ m x) →
      (∀ x, 0 < fX x → DifferentiableAt ℝ m' x) →
      ∃ a : ℝ, HasDerivAt m a (mean μ X) ∧ HasDerivAt m' a (mean μ X)

/-- The mathematical content packaged for target P001-T1. -/
def T1Statement : Prop :=
  FiniteMomentLaw geoMass ∧ massMean geoMass = 1 ∧ massSecond geoMass = 3 ∧
   (∀ n, 2  ≤  n → FiniteMomentLaw (mixMass n) ∧ (∀ k, 0  <  mixMass n k) ∧
     massMean (mixMass n) = 1 + (n : ℝ)⁻¹^2 ∧
     massSecond (mixMass n) = 3 + (n : ℝ)⁻¹ + 2*(n : ℝ)⁻¹^2 ∧
     (massMean (mixMass n) - massMean geoMass) / ((n : ℝ)⁻¹^2) = 1) ∧
   Tendsto (fun (n : ℕ) => massSecond (mixMass n) - (massMean (mixMass n))^2) atTop (nhds 2) ∧
   Tendsto (fun n : ℕ => (n : ℝ)⁻¹^2) atTop (nhds 0) ∧
   (∀ ε : ℝ, 0  <  ε → ∀ᶠ n in atTop, ∀ x : ℝ,
     |(massCDF (mixMass n) x - massCDF geoMass x) / ((n : ℝ)⁻¹^2)|  <  ε)

/-- The mathematical content packaged for target P001-T2. -/
def T2Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
   (hv : 0  <  var μ (X 0)),
  (∀ n, 0  <  n → ∀ ω, mean (empirical X n ω) id = sampleMean X n ω) ∧
   CD μ (fun n ω => Real.sqrt n * (sampleMean X n ω - mean μ (X 0)))
     (gaussianReal 0 ⟨var μ (X 0), le_of_lt hv⟩)) ∧

T1Statement

/-- The mathematical content packaged for target P001-T3. -/
def T3Statement : Prop :=
  ((¬ pda_at_mean_printed_contract) ∧

(IsProbabilityMeasure gapJointLaw ∧
  HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
  gapJointLaw = (gapJointLaw.map Prod.fst).prod (gapJointLaw.map Prod.snd) ∧
  HasPDF (gapJointLaw.map Prod.fst) gapPDF ∧
  gapJointLaw.map Prod.snd = uniformLaw (-1) 1 ∧
  (∀ᵐ xy ∂gapJointLaw, xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1) ∧
  mean gapJointLaw Prod.fst = 0 ∧ gapPDF 0 = 0 ∧
  IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
  ContDiff ℝ 1 pdaBump ∧
  (∀ x, 0 < gapPDF x → pdaBump x = 0) ∧
  deriv (fun _ : ℝ => (0 : ℝ)) 0 = 0 ∧
  (∀ a : ℝ, IsCEF gapJointLaw Prod.fst Prod.snd (fun x => a*pdaBump x) ∧
    deriv (fun x => a*pdaBump x) (mean gapJointLaw Prod.fst) = a)) ∧

(IsProbabilityMeasure gapJointLaw ∧
   HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 * (if xy.2∈Set.Icc (-1 : ℝ) 1 then 1/2 else 0)) ∧
   mean gapJointLaw Prod.fst=0 ∧ IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
   IsCEF gapJointLaw Prod.fst Prod.snd pdaBump ∧
   ContDiff ℝ 1 pdaBump ∧ deriv pdaBump (mean gapJointLaw Prod.fst)=1 ∧
   deriv (fun _ : ℝ => (0 : ℝ)) (mean gapJointLaw Prod.fst)=0)) ∧

ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
({x : ℝ | 0 < gapPDF x} = Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2)


end SAP.P001a
