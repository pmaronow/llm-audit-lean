import SAP.P023.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P023
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def ClusteredPopulation : Prop :=
    (∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ProbabilityLaw (clusteredMargins d) ∧ MarginSupport (clusteredMargins d) ∧
      clusteredMargins d {0}=0 ∧
      (∀ a b : ℝ, -1 ≤ a → a<b → b ≤ 1 → 0 < clusteredMargins d (Set.Ioo a b)) ∧
      Continuous (clusterDensity d) ∧ (∀ x ∈ Set.Icc (-1) 1, d^4/2 ≤ clusterDensity d x) ∧
      Continuous (clusterSmooth d) ∧ clusterSmooth d 0 = 0 ∧
      (∀ x, |x| ≤ 1/2-d → clusterSmooth d x=0) ∧
      (∀ x, clusterSmooth d (-x) = -clusterSmooth d x) ∧
      (∀ x x', |clusterSmooth d x - clusterSmooth d x'| ≤ |x-x'|) ∧
      (∀ x, |clusterSmooth d x| ≤ d/2) ∧
      sSup ((fun x => |clusterSmooth d x|) '' Set.Icc (-1) 1) = d/2 ∧
      ConditionalMean (witnessLaw (clusteredMargins d) (clusterSmooth d)) (fun x => 1/2 + clusterSmooth d x) ∧
      expectation (clusteredMargins d) (fun x => x) = 0 ∧
      expectation (clusteredMargins d) (clusterSmooth d) = 0 ∧
      expectation (clusteredMargins d) (fun x => (party x-1/2)*clusterSmooth d x) = 0 ∧
      expectation (clusteredMargins d) (fun x => x * party x) = 1/4 ∧
      expectation (clusteredMargins d) (fun x => x^2) = (1-d^4)*((1/2)^2+(d/2)^2/6)+d^4/3 ∧
      expectation (clusteredMargins d) (fun x => x * clusterSmooth d x) = (1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3 ∧
      populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x) =
        -(1-d^4+6*d^5)/(1-d^4+2*d^2) ∧
      (∀ k, 0 < k → k < 1/2-d → populationRD (clusteredMargins d) (fun x => 1/2 + clusterSmooth d x) k = 0) ∧
      expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) ≤ (d/2)^2) ∧
    populationCoefficient (clusteredMargins (1/1000)) 1 (fun x => 1/2 + clusterSmooth (1/1000) x) =
      -499999999999503/500000999999500 ∧
    (∀ᵐ z ∂witnessLaw (clusteredMargins (1/1000)) (clusterSmooth (1/1000)),
      799/2000 ≤ z.2 ∧ z.2 ≤ 1201/2000) ∧
    Tendsto (fun d => populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) ∧
    ¬ (∃ C : ℝ, ∀ d, 0 < d → d ≤ 1/2 →
      |populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x)| ≤ C*(d/2))

def ClusteredFit : Prop :=
    ∀ (d : ℝ) (hd : 0 < d ∧ d ≤ 1/2),
    let ν := witnessLaw (clusteredMargins d) (clusterSmooth d)
    ProbabilityLaw ν ∧ marginLaw ν = clusteredMargins d ∧
    predictionRisk ν (fun x => 1/2+clusterSmooth d x) = 1/100 ∧
    predictionRisk ν (fun _ => 1/2) = 1/100+expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) ∧
    (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
      predictionRisk ν (fun _ => 1/2)-predictionRisk ν f ≤ (d/2)^2) ∧
    (∀ J, 1 ≤ J → fittedRisk ν J ≤ predictionRisk ν (fun _ => 1/2) ∧
      (∀ f : ℝ → ℝ, Measurable f → Integrable (fun z => (z.2-f z.1)^2) ν →
        fittedRisk ν J-predictionRisk ν f ≤ (d/2)^2))

def ContinuityWitness : Prop :=
    Tendsto (amplification uniformMargins) atTop atTop ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      |amplification uniformMargins J - (4/Real.pi)*Real.log J| ≤ C) ∧
    (∀ J, 1 ≤ J → sSup {t | ∃ h : ℝ → ℝ, ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1) ∧ t = biasFunctional uniformMargins J h} = amplification uniformMargins J) ∧
    (∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) ∧ StrictMono degrees ∧
      (∀ m, 1 ≤ m → biasFunctional uniformMargins (degrees m) h ≥ (m : ℝ)/4) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) = biasFunctional uniformMargins J h) ∧
      (∀ m, 1 ≤ m → populationCoefficient uniformMargins (degrees m) (fun x => 1/2+h x) ≥ (m : ℝ)/4) ∧
      (∀ B : ℝ, ∀ J₀ : ℕ, ∃ J ≥ J₀,
        B ≤ populationCoefficient uniformMargins J (fun x => 1/2+h x)) ∧
      ContinuousOn (fun x => 1/2+h x) (Set.Icc (-1) 1) ∧ (1/2+h 0 = (1/2 : ℝ)) ∧
      Tendsto (fun m => populationCoefficient uniformMargins (degrees m) (fun x => 1/2+h x)) atTop atTop ∧
      ¬ Tendsto (fun J => populationCoefficient uniformMargins J (fun x => 1/2+h x)) atTop (nhds 0) ∧
      Tendsto (populationRD uniformMargins (fun x => 1/2+h x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ x ∈ Set.Icc (-1) 1, 5/12 ≤ 1/2+h x ∧ 1/2+h x ≤ 7/12) ∧
      ¬ (∃ L : ℝ, ∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1, |h x-h x'| ≤ L*|x-x'|))

def PopulationBias : Prop :=
    ∀ (ν : Measure (ℝ × ℝ))
    (hprob : ProbabilityLaw ν) (hsupport : MarginSupport (marginLaw ν))
    (hsq : Integrable (fun z => z.2^2) ν) (α β : ℝ) (h : ℝ → ℝ)
    (hm : Measurable h) (hb : ∃ B, ∀ x ∈ Set.Icc (-1) 1, |h x| ≤ B)
    (hmean : ConditionalMean ν (fun x => α + β * party x + h x))
    (J : ℕ) (hJ : 1 ≤ J) (hpd : MomentPositiveDefinite (marginLaw ν) J),
    let μ := marginLaw ν
    let v := residualVariance μ J
    let b := populationCoefficient μ J (fun x => α + β * party x + h x)
    IsProjection μ J (projection μ J) ∧ 0 < v ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => popResidual μ J x * p.eval x) = 0) ∧
    expectation μ (popResidual μ J) = 0 ∧
    expectation μ (fun x => popResidual μ J x * party x) = v ∧
    b = biasFunctional μ J (fun x => α + β * party x + h x) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      b - β = biasFunctional μ J h ∧
      b - β = biasFunctional μ J (fun x => h x - p.eval x) ∧
      |b - β| ≤ amplification μ J * supError h p ∧
      |b - β| ≤ rmsError μ h p / Real.sqrt v) ∧
    2 ≤ amplification μ J ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      (∀ᵐ x ∂μ, h x = p.eval x) → b = β) ∧
    (∀ t > 0, (|b - β| ≤ t ↔ |expectation μ (fun x => popResidual μ J x * h x)| ≤ t * v) ∧
      (amplification μ J * sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = supError h p} ≤ t → |b - β| ≤ t) ∧
      (sInf {e | ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ e = rmsError μ h p} ≤ t * Real.sqrt v → |b - β| ≤ t))

def UniformConstants : Prop :=
    ProbabilityLaw uniformMargins ∧ MarginSupport uniformMargins ∧
    (∀ J, 1 ≤ J → residualVariance uniformMargins J = centralBinomial ((J + 1) / 2)^2 / 4) ∧
    (∀ x, (projection uniformMargins 1).eval x = projection1 x) ∧
    (∀ x, (projection uniformMargins 7).eval x = projection7 x) ∧
    residualVariance uniformMargins 1 = 1 / 16 ∧
    residualVariance uniformMargins 7 = 1225 / 65536 ∧
    expectation uniformMargins (fun x => |popResidual uniformMargins 1 x|) = 5 / 24 ∧
    amplification uniformMargins 1 = 10 / 3 ∧
    1 / Real.sqrt (residualVariance uniformMargins 1) = 4 ∧
    1 / Real.sqrt (residualVariance uniformMargins 7) = 256 / 35 ∧
    (47642006857252250 / 10000000000000000 : ℝ) < amplification uniformMargins 7 ∧
    amplification uniformMargins 7 < (47642006857252260 / 10000000000000000 : ℝ)

def FiniteConditionalBias : Prop :=
    ∀ {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hprob : ProbabilityLaw P)
    (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ) (hdata : TwoParty x d)
    (hd : ∀ i, d i = party (x i))
    (hfull : FullRank (polynomialDesign J x d)) (α β : ℝ) (h : ℝ → ℝ)
    (Y : ι → Ω → ℝ) (hint : ∀ i, Integrable (Y i) P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = α+β*d i+h (x i)),
    0 < dot (finiteResidual J x d) (finiteResidual J x d) ∧
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) - β =
      dot (finiteResidual J x d) (fun i => h (x i)) /
        dot (finiteResidual J x d) (finiteResidual J x d)

def CorrectedAsymptotics : Prop :=
    ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (α β : ℝ) (h : ℝ → ℝ) (c δ L σ2 : ℝ)
    (hr : RepairedRegularity ν α β h c δ L σ2) (hiid : IIDSample P ν sample)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N)
    (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N : ℝ) * k N) atTop atTop)
    (_hRDvalid : RDAdmissible P sample k)
    (_hOLSfixed : ∀ J, 1 ≤ J → OLSAdmissible P sample (fun _ => J))
    (_hOLSgrowing : ∀ degrees : ℕ → ℕ, Tendsto degrees atTop atTop →
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue (marginLaw ν) (degrees N))^3))
        atTop (nhds 0) → OLSAdmissible P sample degrees),
    let μ := marginLaw ν
    let m := fun x => α + β*party x + h x
    (∀ J, 1 ≤ J → MomentPositiveDefinite μ J ∧
      residualVariance μ J ≥ c*δ/(4*((J:ℝ)+1))) ∧
    (∀ J, 1 ≤ J → ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ p.eval 0 = 0 ∧
      supError h p ≤ 4*jacksonK*L/((J:ℝ)+1)) ∧
    (∀ J, 1 ≤ J → |populationCoefficient μ J m - β| ≤
      8*jacksonK*L / Real.sqrt (c*δ*((J:ℝ)+1))) ∧
    Tendsto (fun J => populationCoefficient μ J m) atTop (nhds β) ∧
    (∀ J, 1 ≤ J → ConvergesInProbability P (fun N => samplePolynomial sample N J) (populationCoefficient μ J m)) ∧
    (∀ k', 0 < k' → k' ≤ δ → |populationRD μ m k' - β| ≤ 2*L*k') ∧
    ConvergesInProbability P (sampleRD sample k) β ∧
    (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient μ J m - β) ∧ |populationCoefficient μ J m - β| < ε) ∧
    (∀ degrees : ℕ → ℕ, Tendsto degrees atTop atTop →
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0) →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω -
        populationCoefficient μ (degrees N) m) 0 ∧
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω - sampleRD sample k N ω) 0) ∧
    (∃ degrees : ℕ → ℕ, (∀ N, 1 ≤ degrees N) ∧ Tendsto degrees atTop atTop ∧
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0))

def PairIndexedAppendix : Prop :=
    ∀ (S : Finset (ℕ × ℕ))
    (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : {p : ℕ × ℕ // p ∈ S} → ℝ) (hdata : TwoParty x d)
    (hc : Condition1 k x) (β : ℝ) (hβ : CoarsenedOLS k x d y β),
    let B := fun p => binLabel k (x p)
    let r := demeaned B d
    let z := demeaned B y
    (∀ p j, inBin k j.val (x p) ↔ B p = j) ∧
    (binSet B (centralLabel k) = close k x) ∧
    (∀ p, p ∉ close k x → r p = 0) ∧
    0 < (∑ p ∈ close k x, r p^2) ∧
    β = (∑ p ∈ close k x, r p^2)⁻¹ * (∑ p ∈ close k x, r p*z p)

def CoarsenedLocalization : Prop :=
    ∀ {ι : Type} [Fintype ι] (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y y' : ι → ℝ) (hdata : TwoParty x d)
    (hn1 : 0 < ∑ i ∈ close k x, d i) (hn0 : 0 < ∑ i ∈ close k x, (1-d i))
    (hag : ∀ i ∈ close k x, y i = y' i) (β β' : ℝ)
    (hβ : CoarsenedOLS k x d y β) (hβ' : CoarsenedOLS k x d y' β'),
    β = β'

def PolynomialLocalizationRefutation : Prop :=
    ¬ (∀ (n J : ℕ) (x d : Fin n → ℝ) (k : ℝ),
      1 ≤ J → 0 < k → k < 1 → TwoParty x d → Condition1 k x →
      FullRank (polynomialDesign J x d) →
      (∃ c : Fin (J + 2) → ℝ, ∀ i, 0 < predict (polynomialDesign J x d) c i ∧
        predict (polynomialDesign J x d) c i < 1) →
      Localized k x (polynomialOLS J x d))

def PropositionOne : Prop :=
    ∀ {ι : Type} [Fintype ι] (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (h1 : Condition1 k x)
    (c : Fin (binCount k+2) → ℝ) (hc : IsOLS (coarsenedDesign k x d) y c),
    c ⟨1, by omega⟩=rd k x d y

end
end SAP.P023
