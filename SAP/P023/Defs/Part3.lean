import SAP.P023.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def LinearWitness : Prop :=
    TwoParty linearX linearD ∧ Condition1 (1 / 200 : ℝ) linearX ∧
    FullRank (polynomialDesign 1 linearX linearD) ∧
    linearY = predict (polynomialDesign 1 linearX linearD) linearExact ∧
    (∀ z, polynomialOLS 1 linearX linearD z = dot linearW z) ∧
    polynomialOLS 1 linearX linearD linearY = 1/10 ∧
    polynomialOLS 1 linearX linearD linearYprime = (1371721 / 13920200 : ℝ) ∧
    polynomialOLS 1 linearX linearD linearYprime - polynomialOLS 1 linearX linearD linearY = (-20299 / 13920200 : ℝ) ∧
    (-20299 / 13920200 : ℝ) ≠ 0 ∧
    (∀ i ∈ close (1 / 200 : ℝ) linearX, linearY i = linearYprime i) ∧
    (∀ i, linearYprime i = linearY i + if i = 5 then 1/100 else 0) ∧
    rd (1 / 200 : ℝ) linearX linearD linearY = (401 / 4000 : ℝ) ∧
    rd (1 / 200 : ℝ) linearX linearD linearYprime = (401 / 4000 : ℝ) ∧
    binCount (1 / 200 : ℝ) = 200 ∧
    (∀ i, (binLabel (1 / 200 : ℝ) (linearX i)).val = ![25, 75, 100, 100, 125, 175] i) ∧
    CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY (401 / 4000 : ℝ) ∧
    CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime (401 / 4000 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY β → β = (401 / 4000 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime β → β = (401 / 4000 : ℝ)) ∧
    (∀ i, 0 < linearY i ∧ linearY i < 1 ∧ 0 < linearYprime i ∧ linearYprime i < 1) ∧
    ¬ Localized (1 / 200 : ℝ) linearX (polynomialOLS 1 linearX linearD)

def DegreeSevenWitness : Prop :=
    TwoParty degree7X degree7D ∧ Condition1 (1 / 5 : ℝ) degree7X ∧
    FullRank (polynomialDesign 7 degree7X degree7D) ∧
    degree7Y = predict (polynomialDesign 7 degree7X degree7D) degree7Exact ∧
    (∀ z, polynomialOLS 7 degree7X degree7D z = dot degree7W z) ∧
    polynomialOLS 7 degree7X degree7D degree7Y = 1/10 ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime = (3249 / 32140 : ℝ) ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime - polynomialOLS 7 degree7X degree7D degree7Y = (7 / 6428 : ℝ) ∧
    (7 / 6428 : ℝ) ≠ 0 ∧
    (∀ i ∈ close (1 / 5 : ℝ) degree7X, degree7Y i = degree7Yprime i) ∧
    (∀ i, degree7Yprime i = degree7Y i + if i = 15 then 1/100 else 0) ∧
    rd (1 / 5 : ℝ) degree7X degree7D degree7Y = (11796481 / 104857600 : ℝ) ∧
    rd (1 / 5 : ℝ) degree7X degree7D degree7Yprime = (11796481 / 104857600 : ℝ) ∧
    binCount (1 / 5 : ℝ) = 4 ∧
    (∀ i, (binLabel (1 / 5 : ℝ) (degree7X i)).val = ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4] i) ∧
    CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y (11796481 / 104857600 : ℝ) ∧
    CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime (11796481 / 104857600 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y β → β = (11796481 / 104857600 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime β → β = (11796481 / 104857600 : ℝ)) ∧
    (∀ i, 0 < degree7Y i ∧ degree7Y i < 1 ∧ 0 < degree7Yprime i ∧ degree7Yprime i < 1) ∧
    ¬ Localized (1 / 5 : ℝ) degree7X (polynomialOLS 7 degree7X degree7D) ∧ (∀ i, degree7W i ≠ 0)

def UniformIllustration : Prop :=
    (∀ x, (projection uniformMargins 1).eval x = projection1 x) ∧
    (∀ x, (projection uniformMargins 7).eval x = projection7 x) ∧
    residualVariance uniformMargins 1 = 1/16 ∧ residualVariance uniformMargins 7 = 1225/65536 ∧
    popResidual uniformMargins 1 (9/10) / residualVariance uniformMargins 1 = -14/5 ∧
    popResidual uniformMargins 7 (9/10) / residualVariance uniformMargins 7 = -20283449/6125000 ∧
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 1 x^2 else 0) /
      residualVariance uniformMargins 1 = 1/8 ∧
    expectation uniformMargins (fun x => if 1/2 ≤ |x| then popResidual uniformMargins 7 x^2 else 0) /
      residualVariance uniformMargins 7 = 572158921/10276044800 ∧
    populationCoefficient uniformMargins 1 (fun x => 1/2 + (1/10)*party x + x/20) = 1/10 ∧
    populationCoefficient uniformMargins 7 (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) = 1/10 ∧
    (∀ k, 0 < k → k ≤ 1 →
      populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20) k = 1/10+k/20 ∧
      populationRD uniformMargins (fun x => 1/2 + (1/10)*party x + x/20+x^7/100) k = 1/10+k/20+k^7/400) ∧
    Tendsto (populationRD uniformMargins (fun x => 1/2 + (1/10)*party x+x/20)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/10)) ∧
    Tendsto (populationRD uniformMargins (fun x => 1/2 + (1/10)*party x+x/20+x^7/100)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/10))

def PrintedBinEquivalence : Prop :=
    ∀ {ι : Type} [Fintype ι] (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (β : ℝ),
    CoarsenedOLS k x d y β ↔ ∃ c : Fin (binCount k+2) → ℝ,
      IsOLS (coarsenedDesign k x d) y c ∧ c ⟨1, by omega⟩=β

def CoarsenedWeights : Prop :=
    ∀ {ι : Type} [Fintype ι] (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d)
    (hn1 : 0 < ∑ i ∈ close k x, d i) (hn0 : 0 < ∑ i ∈ close k x, (1-d i))
    (β : ℝ) (hβ : CoarsenedOLS k x d y β),
    β = dot (coarsenedWeight k x d) y ∧ β = rd k x d y ∧
    (∀ i, i ∉ close k x → coarsenedWeight k x d i = 0) ∧
    (∀ i ∈ close k x, d i = 1 → coarsenedWeight k x d i = 1 / (∑ l ∈ close k x, d l)) ∧
    (∀ i ∈ close k x, d i = 0 → coarsenedWeight k x d i = -1 / (∑ l ∈ close k x, (1-d l)))

def ConditionalMoments : Prop :=
    ∀ {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hprob : P Set.univ = 1)
    (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ) (hdata : TwoParty x d)
    (hfull : FullRank (polynomialDesign J x d)) (α β : ℝ) (h : ℝ → ℝ)
    (Y : ι → Ω → ℝ) (hint : ∀ i, MeasureTheory.Integrable (Y i) P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = α + β*d i+h (x i)),
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) - β =
      dot (finiteResidual J x d) (fun i => h (x i)) /
        dot (finiteResidual J x d) (finiteResidual J x d) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J → (∀ i, h (x i) = p.eval (x i)) →
      (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) = β) ∧
    (let u := fun i ω => Y i ω - (α+β*d i+h (x i))
     (∀ i, MeasureTheory.Integrable (fun ω => u i ω^2) P) →
     (∀ i l, i ≠ l → (∫ ω, u i ω * u l ω ∂P) = 0) →
     (∫ ω, (polynomialOLS J x d (fun i => Y i ω) -
       (∫ ω', polynomialOLS J x d (fun i => Y i ω') ∂P))^2 ∂P) =
       ∑ i, (finiteWeight J x d i)^2 * (∫ ω, u i ω^2 ∂P)) ∧
    (∀ i (σ2 : ℝ), finiteWeight J x d i ≠ 0 → 0 < σ2 → 0 < (finiteWeight J x d i)^2*σ2)

def FiniteNonlocality : Prop :=
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 1 ≤ J) (k : ℝ) (hk : 0 < k ∧ k < 1) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d))
    (hboth : (∃ i, d i = 1) ∧ (∃ i, d i = 0))
    (_hn1 : 0 < ∑ i ∈ close k x, d i)
    (_hn0 : 0 < ∑ i ∈ close k x, (1-d i)),
    ((Finset.univ.filter (fun i => x i < 0 ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    ((Finset.univ.filter (fun i => 0 < x i ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    (((Finset.univ.filter (fun i => i ∉ close k x ∧ x i ≠ 0)).image x).card > 2*J →
      ∃ (i : ι) (y y' : ι → ℝ), i ∉ close k x ∧
      (∀ l, l ≠ i → y l = y' l) ∧ (∀ l ∈ close k x, y l = y' l) ∧
      polynomialOLS J x d y ≠ polynomialOLS J x d y' ∧ rd k x d y = rd k x d y' ∧
      (∀ β β', CoarsenedOLS k x d y β → CoarsenedOLS k x d y' β' →
        (0 < ∑ l ∈ close k x, d l) → (0 < ∑ l ∈ close k x, (1-d l)) → β = β'))

def FinitePolynomialWeights : Prop :=
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d)),
    let r := finiteResidual J x d
    let w := finiteWeight J x d
    dot r d = dot r r ∧ 0 < dot r r ∧
    (∀ j ≤ J, dot r (fun i => x i^j) = 0) ∧
    (∀ y, polynomialOLS J x d y = dot r y / dot r r ∧ polynomialOLS J x d y = dot w y) ∧
    (∑ i, w i) = 0 ∧ (∀ j, 1 ≤ j → j ≤ J → (∑ i, w i*x i^j) = 0) ∧
    (∑ i, w i*d i) = 1 ∧
    (∀ (y : ι → ℝ) (i : ι) (δ : ℝ),
      polynomialOLS J x d (fun l => y l + if l = i then δ else 0) - polynomialOLS J x d y = w i*δ)

def SharedConsistency : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ) (J : ℕ) (k : ℕ → ℝ) (β : ℝ)
    (_hprob : ProbabilityLaw P) (_hJ : 1 ≤ J) (_hk : ∀ N, 0 < k N)
    (_hOLSvalid : OLSAdmissible P sample (fun _ => J))
    (_hRDvalid : RDAdmissible P sample k)
    (hOLS : ConvergesInProbability P (fun N => samplePolynomial sample N J) β)
    (hRD : ConvergesInProbability P (sampleRD sample k) β),
    ConvergesInProbability P
      (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω) 0

def SigmoidPopulation : Prop :=
    (∀ a η : ℝ, 0 < a → 0 < η → η ≤ 1 →
      Continuous (sigmoid a η) ∧ sigmoid a η 0 = 0 ∧
      (∀ x, sigmoid a η (-x) = -sigmoid a η x) ∧
      (∀ x x', |sigmoid a η x - sigmoid a η x'| ≤ (a / η) * |x - x'|) ∧
      ConditionalMean (witnessLaw uniformMargins (sigmoid a η)) (fun x => 1 / 2 + sigmoid a η x) ∧
      (∀ k, 0 < k → k ≤ η → populationRD uniformMargins (fun x => 1 / 2 + sigmoid a η x) k = a*k/η) ∧
      Tendsto (populationRD uniformMargins (fun x => 1 / 2 + sigmoid a η x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1 / 2 + sigmoid a η x) =
        2*a - (a / residualVariance uniformMargins J) *
          (∫ x in Set.Icc 0 η, popResidual uniformMargins J x * (1 - x/η))) ∧
      populationCoefficient uniformMargins 1 (fun x => 1 / 2 + sigmoid a η x) = 2*a*(1-η)^2 ∧
      expectation uniformMargins (fun x => (sigmoid a η x - a*(2*party x-1))^2) = a^2*η/3 ∧
      (∀ J, 1 ≤ J →
        0 ≤ sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
          (fun x => (1 / 2 + sigmoid a η x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ∧
        sInf {e | ∃ c : Fin (J+2) → ℝ, e = expectation uniformMargins
          (fun x => (1 / 2 + sigmoid a η x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)^2)} ≤ a^2*η/3)) ∧
    populationCoefficient uniformMargins 1 (fun x => 1 / 2 + sigmoid (1 / 20) (1 / 10000) x) = 99980001 / 1000000000 ∧
    populationCoefficient uniformMargins 7 (fun x => 1 / 2 + sigmoid (1 / 20) (1 / 10000) x) =
      4896723787999993532000048047999857 / 49000000000000000000000000000000000 ∧
    (∀ᵐ z ∂witnessLaw uniformMargins (sigmoid (1 / 20) (1 / 10000)), 7 / 20 ≤ z.2 ∧ z.2 ≤ 13 / 20) ∧
    ((1 / 20 : ℝ)^2 * (1 / 10000) / 3 = 1 / 12000000) ∧
    (∀ J a, 1 ≤ J → 0 < a →
      Tendsto (fun η => populationCoefficient uniformMargins J (fun x => 1 / 2 + sigmoid a η x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (2*a)))

def SigmoidFit : Prop :=
    ∀ (a η : ℝ) (ha : 0 < a) (hη : 0 < η ∧ η ≤ 1),
    let ν := witnessLaw uniformMargins (sigmoid a η)
    ProbabilityLaw ν ∧ marginLaw ν = uniformMargins ∧
    predictionRisk ν (fun x => 1/2+sigmoid a η x) = 1/100 ∧
    (∀ J, 1 ≤ J → 1/100 ≤ fittedRisk ν J ∧ fittedRisk ν J ≤ 1/100+a^2*η/3 ∧
      (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
        fittedRisk ν J - predictionRisk ν f ≤ a^2*η/3) ∧
      (fittedRisk ν J-1/100)/(fittedRisk ν J) ≤ 100*a^2*η/3) ∧
    (a=1/20 → populationCoefficient uniformMargins 7 (fun x => 1/2+sigmoid a η x) =
      1/10-(4096/6125)*η+(6/5)*η^2-(33/25)*η^4+(858/875)*η^6-(143/490)*η^8)

def SigmoidSampling : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P (witnessLaw uniformMargins (sigmoid (1/20) (1/10000))) sample)
    (k : ℕ → ℝ) (hpos : ∀ N, 0 < k N) (hk : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N:ℝ)*k N) atTop atTop)
    (_hOLS1 : OLSAdmissible P sample (fun _ => 1))
    (_hOLS7 : OLSAdmissible P sample (fun _ => 7))
    (_hRDvalid : RDAdmissible P sample k),
    ConvergesInProbability P (fun N => samplePolynomial sample N 1) (99980001/1000000000) ∧
    ConvergesInProbability P (fun N => samplePolynomial sample N 7)
      (4896723787999993532000048047999857/49000000000000000000000000000000000) ∧
    ConvergesInProbability P (sampleRD sample k) 0

def UniformSymmetry : Prop :=
    (∀ J, 1 ≤ J → ∀ x, x ≠ 0 → popResidual uniformMargins J (-x) = -popResidual uniformMargins J x) ∧
    (∀ x, 0<x → popResidual uniformMargins 1 x=1/2-(3/4)*x ∧
      popResidual uniformMargins 7 x=1/2-(11025*x-40425*x^3+63063*x^5-32175*x^7)/4096)

end
end SAP.P023
