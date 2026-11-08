import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a

def prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ := (μ A).toReal

def mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

def var {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ProbabilityTheory.variance X μ

def cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := prob μ {ω | X ω  ≤  x}

def CP {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε : ℝ, 0  <  ε → Tendsto (fun (n : ℕ) => prob μ {ω | ε  ≤  dist (Z n ω) c}) atTop (nhds 0)

def CD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ) (ν : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun t => prob ν (Set.Iic t)) x →
    Tendsto (fun (n : ℕ) => cdf μ (Z n) x) atTop (nhds (prob ν (Set.Iic x)))

def IID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, IdentDistrib (X i) (X 0) μ μ

def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)

def empirical {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (X i ω)

def HasPDF (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0  ≤  f x) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

def IsCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧ ∀ A : Set E, MeasurableSet A →
    (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

structure FiniteLaw (n : ℕ) where
  weight : Fin n → ℝ
  nonneg : ∀ i, 0  ≤  weight i
  total : ∑ i, weight i = 1

def fmean {n : ℕ} (P : FiniteLaw n) (X : Fin n → ℝ) : ℝ := ∑ i, P.weight i * X i

def fprob {n : ℕ} (P : FiniteLaw n) (A : Fin n → Prop) [DecidablePred A] : ℝ :=
  ∑ i, if A i then P.weight i else 0

def geoMass (k : ℕ) : ℝ := (1/2 : ℝ)^(k+1)

def massCDF (q : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, if (k : ℝ)  ≤  x then q k else 0

def mixMass (n k : ℕ) : ℝ :=
  (1 - (n : ℝ)⁻¹^3)*geoMass k + (n : ℝ)⁻¹^3 *
    (if n  ≤  k then geoMass (k-n) else 0)

def massMean (q : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ)*q k

def massSecond (q : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ)^2*q k

def FiniteMomentLaw (q : ℕ → ℝ) : Prop :=
  (∀ k, 0  ≤  q k) ∧ Summable q ∧ (∑' k, q k) = 1 ∧
    Summable (fun k : ℕ => (k : ℝ)*q k) ∧ Summable (fun k : ℕ => (k : ℝ)^2*q k)

def gapPDF (x : ℝ) : ℝ := if x ∈ Set.Icc (-2) (-1) ∪ Set.Icc 1 2 then 1/2 else 0

def pdaBump (x : ℝ) : ℝ := if |x|  <  1 then x*(1-x^2)^2 else 0

def partialAt {K : ℕ} (m : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) (k : Fin K) : ℝ :=
  deriv (fun t : ℝ => m (Function.update x k (x k + t))) 0

def IsSieveLS {Ω : Type*} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (fit : ℕ → Ω → Polynomial ℝ) : Prop :=
  ∀ n ω, (fit n ω).natDegree  ≤  J n ∧ ∀ p : Polynomial ℝ, p.natDegree  ≤  J n →
    (∑ i ∈ Finset.range n, (Y i ω - (fit n ω).eval (X i ω))^2)  ≤ 
      ∑ i ∈ Finset.range n, (Y i ω - p.eval (X i ω))^2

def uniformLaw (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (if x ∈ Set.Icc a b then (b-a)⁻¹ else 0))

def bernoulliKL (p t : ℝ) : ℝ := p*Real.log (p/t)+(1-p)*Real.log ((1-p)/(1-t))

def clip (a b x : ℝ) : ℝ := max a (min b x)

def normalDensity (m s y : ℝ) : ℝ :=
  Real.exp (-(y-m)^2/(2*s^2))/(s*Real.sqrt (2*Real.pi))

def lognormalDensity (m s y : ℝ) : ℝ :=
  if 0  <  y then normalDensity m s (Real.log y)/y else 0

def exponentialDensity (r y : ℝ) : ℝ :=
  if 0  ≤  y then r*Real.exp (-r*y) else 0

def mixtureDensity (θ : Fin 7 → ℝ) (y : ℝ) : ℝ :=
  θ 0*normalDensity (θ 2) (θ 3) y + θ 1*lognormalDensity (θ 4) (θ 5) y +
    (1-θ 0-θ 1)*exponentialDensity (θ 6) y

def MixtureAdmissible (θ : Fin 7 → ℝ) : Prop :=
  0  ≤  θ 0 ∧ 0  ≤  θ 1 ∧ θ 0+θ 1  ≤  1 ∧ 0  <  θ 3 ∧ 0  <  θ 5 ∧ 0  <  θ 6

def mixtureLikelihood {n : ℕ} (y : Fin n → ℝ) (θ : Fin 7 → ℝ) : ℝ := ∏ i, mixtureDensity θ (y i)

def mixtureRestriction (B S δ a b : ℝ) : Set (Fin 7 → ℝ) :=
  {θ | MixtureAdmissible θ ∧ |θ 2|  ≤  B ∧ |θ 4|  ≤  B ∧
    δ  ≤  θ 3 ∧ θ 3  ≤  S ∧ δ  ≤  θ 5 ∧ θ 5  ≤  S ∧ a  ≤  θ 6 ∧ θ 6  ≤  b}

def disjointMixture (p a b : ℝ) : Fin 4 → ℝ := ![p*(1-a),p*a,(1-p)*(1-b),(1-p)*b]

def nearestDonor {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool) (i : Fin n) : Option (Fin n) :=
  if h : ∃ j, r j = true ∧ ∀ k, r k = true → |p j-p i|  ≤  |p k-p i|
    then some (Classical.choose h) else none

def noise (b : Bool) : ℝ := if b then 1 else -1

def hotDeck {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  if ∃ j, (s j).2.1 = true then
    (∑ i, if (s i).2.1 then 50+noise (s i).2.2 else
      match nearestDonor (fun j => (s j).1) (fun j => (s j).2.1) i with
      | some j => 50+noise (s j).2.2
      | none => 50) / (n : ℝ)
  else 50

def causalMatch {n : ℕ} (s : Fin n → ℝ × Bool × Bool) : ℝ :=
  -(∑ i, if (s i).2.1 then
      match nearestDonor (fun j => (s j).1) (fun j => !(s j).2.1) i with
      | some j => noise (s j).2.2
      | none => 0
    else noise (s i).2.2) / (n : ℝ)

def resample {n : ℕ} {E : Type*} (s : Fin n → E) (a : Fin n → Fin n) : Fin n → E := s ∘ a

def bootMean {n : ℕ} {E : Type*} (T : (Fin n → E) → ℝ) (s : Fin n → E) : ℝ :=
  (∑ a : Fin n → Fin n, T (resample s a)) / ((n : ℝ)^n)

def bootVar {n : ℕ} {E : Type*} (T : (Fin n → E) → ℝ) (s : Fin n → E) : ℝ :=
  (∑ a : Fin n → Fin n, (T (resample s a) - bootMean T s)^2) / ((n : ℝ)^n)

def matchingUnitLaw : Measure (ℝ × Bool × Bool) :=
  (volume.prod (Measure.count.prod Measure.count)).withDensity
    (fun u => ENNReal.ofReal (if u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)
      then (if u.2.1 then u.1 else 1-u.1) else 0))

def matchV : ℝ := 3*Real.log 3-1/4

def matchS : ℝ := 1-Real.exp (-1)

def matchA : ℝ := 2/matchS-matchS/(2-matchS)

def matchB : ℝ := 3/(2*matchS)-(4-matchS)/(2*(2-matchS))

def matchVB : ℝ := 1/2+matchA/2+matchB*(2*Real.log 3-3/2)

def firstSample {Ω E : Type*} (Z : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Fin n → E :=
  fun i => Z i ω

def MatchingFailure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ × Bool × Bool) (causal : Bool) : Prop :=
  let T : ∀ n : ℕ, (Fin n → ℝ × Bool × Bool) → ℝ :=
    if causal then fun _ => causalMatch else fun _ => hotDeck
  let θ : ℝ := if causal then 0 else 50
  (∀ n, 0  <  n → mean μ (fun ω => T n (firstSample Z n ω)) = θ) ∧
  Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => T n (firstSample Z n ω))) atTop (nhds matchV) ∧
  Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω))) atTop (nhds matchVB) ∧
  0  <  matchVB ∧ matchVB  <  matchV ∧
  ¬ CP μ (fun n ω => (n : ℝ)*bootVar (T n) (firstSample Z n ω)) matchV

def fcond {n : ℕ} (P : FiniteLaw n) (Y X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if X i=x then P.weight i*Y i else 0) / fprob P (fun i => X i=x)

def FCondIndep {n : ℕ} {E F G : Type*} (P : FiniteLaw n)
    (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) : Prop :=
  ∀ (x : G) (y : E) (z : F), 0  <  fprob P (fun i => X i=x) →
    fprob P (fun i => X i=x ∧ Y i=y ∧ Z i=z) * fprob P (fun i => X i=x) =
    fprob P (fun i => X i=x ∧ Y i=y)*fprob P (fun i => X i=x ∧ Z i=z)

def placeboLaw : FiniteLaw 12 where
  weight i := if i.val/4=1 then (if i.val%2=1 then 1/24 else 1/8)
    else (if i.val%2=1 then 1/8 else 1/24)
  nonneg := by intro i; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

def placeboX (i : Fin 12) : ℝ := if i.val/4=0 then -1 else if i.val/4=1 then 0 else 1

def placeboZ (i : Fin 12) : ℝ := if i.val%4 < 2 then -1 else 1

def placeboD (i : Fin 12) : ℝ := if i.val%2=1 then 1 else 0

def placeboW (i : Fin 12) : ℝ := (placeboX i)^2 + placeboZ i/2

def CI {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    (μ[(fun ω => if Y ω∈A ∧ Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) =ᵐ[μ]
    (fun ω => (μ[(fun ω => if Y ω∈A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω *
      (μ[(fun ω => if Z ω∈B then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]) ω)

def linearPredictor {K : ℕ} (b : Fin (K+1) → ℝ) (x : Fin K → ℝ) : ℝ :=
  b 0 + ∑ k, b k.succ * x k

def overlapT (k : ℕ) : ℝ := (1/3 : ℝ)^(k+1)

def overlapC (k : ℕ) : ℝ := (1/2 : ℝ)^(k+2)

def overlapPropensity (k : ℕ) : ℝ := overlapT k/(overlapT k+overlapC k)

def HasJointPDF (ν : Measure (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
    ν=volume.withDensity (fun x => ENNReal.ofReal (f x))

def WeakLimit {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun (n : ℕ) => mean μ (fun ω => f (Z n ω))) atTop (nhds (mean ν f))

def olsRSS {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ) : ℝ :=
  ∑ i,(Y i-(X.mulVec b) i)^2

def olsCoef {n K : ℕ} (X : Matrix (Fin n) (Fin K) ℝ) (Y : Fin n → ℝ) : Fin K → ℝ :=
  (X.transpose*X)⁻¹.mulVec (X.transpose.mulVec Y)

def robustCov {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (e : Fin n → ℝ) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
  (X.transpose*X)⁻¹*(X.transpose*Matrix.diagonal (fun i => (e i)^2)*X)*(X.transpose*X)⁻¹

def conditionalModelLaw {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ) : Measure ((Fin K → ℝ) × ℝ) :=
  (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (g xy.2 xy.1 θ))

def conditionalKL {K τ : ℕ} (κ : Measure ℝ) (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (x : Fin K → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∫ y,f y x*Real.log (f y x/g y x t) ∂κ

def averageKL {K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (f : ℝ → (Fin K → ℝ) → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ) : ℝ :=
  ∫ x,conditionalKL κ f g x t ∂νX

def placeboFStatistic {n K L : ℕ} (X : Fin n → Fin K → ℝ) (W : Fin n → Fin L → ℝ) (D : Fin n → ℝ) : ℝ :=
  let R : Matrix (Fin n) (Fin (K+1)) ℝ := fun i => Fin.cases 1 (X i)
  let F : Matrix (Fin n) (Fin (K+L+1)) ℝ := fun i => Fin.cases 1 (Fin.addCases (X i) (W i))
  let rr := olsRSS R D (olsCoef R D)
  let rf := olsRSS F D (olsCoef F D)
  ((rr-rf)/(L : ℝ))/(rf/((n : ℝ)-(K+L+1 : ℕ)))

def fReference (k v : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (k+v) => gaussianReal 0 1)).map (fun z =>
    ((∑ i : Fin (k+v),if i.val < k then (z i)^2 else 0)/(k : ℝ))/
      ((∑ i : Fin (k+v),if k ≤ i.val then (z i)^2 else 0)/(v : ℝ)))

def gapJointLaw : Measure (ℝ × ℝ) :=
  (volume.withDensity (fun x => ENNReal.ofReal (gapPDF x))).prod (uniformLaw (-1) 1)

def sampleGram {K : ℕ} {Ω : Type*} (p : Fin K → Polynomial ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => (∑ i∈Finset.range n,(p j).eval (X i ω)*(p k).eval (X i ω))/(n : ℝ)

def gramDeviation {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin K → ℝ,(∑ k,(v k)^2)=1 ∧
    r=|(∑ j,∑ k,v j*G j k*v k)-1|}

def conditionalMeanAt {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (Y : Ω → ℝ) (x : E) : ℝ :=
  (∫ ω in {ω | X ω=x},Y ω ∂μ)/prob μ {ω | X ω=x}


end SAP.P001a
